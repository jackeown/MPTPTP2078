%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XIEdVlLvPN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:53 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 203 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  619 (2266 expanded)
%              Number of equality atoms :   63 ( 154 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X11
        = ( k2_tarski @ X9 @ X10 ) )
      | ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11
        = ( k1_tarski @ X9 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('43',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','38','51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XIEdVlLvPN
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 592 iterations in 0.246s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.69  thf(t64_funct_2, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.69         ( m1_subset_1 @
% 0.47/0.69           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.69       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.69         ( r1_tarski @
% 0.47/0.69           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.69           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.69            ( m1_subset_1 @
% 0.47/0.69              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.69          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.69            ( r1_tarski @
% 0.47/0.69              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.69              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (~ (r1_tarski @ 
% 0.47/0.69          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.47/0.69          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.47/0.69           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf(t144_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X22 : $i, X23 : $i]:
% 0.47/0.69         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.47/0.69          | ~ (v1_relat_1 @ X22))),
% 0.47/0.69      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc2_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.69  thf('7', plain,
% 0.47/0.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.47/0.69         ((v4_relat_1 @ X30 @ X31)
% 0.47/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.69  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.69  thf(d18_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      (![X20 : $i, X21 : $i]:
% 0.47/0.69         (~ (v4_relat_1 @ X20 @ X21)
% 0.47/0.69          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.47/0.69          | ~ (v1_relat_1 @ X20))),
% 0.47/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_D @ 
% 0.47/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc1_relset_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.69       ( v1_relat_1 @ C ) ))).
% 0.47/0.69  thf('12', plain,
% 0.47/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.69         ((v1_relat_1 @ X27)
% 0.47/0.69          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.69  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.47/0.69      inference('demod', [status(thm)], ['10', '13'])).
% 0.47/0.69  thf(t69_enumset1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.69  thf('15', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf(l45_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.47/0.69       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.47/0.69            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.69         (((X11) = (k2_tarski @ X9 @ X10))
% 0.47/0.69          | ((X11) = (k1_tarski @ X10))
% 0.47/0.69          | ((X11) = (k1_tarski @ X9))
% 0.47/0.69          | ((X11) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_tarski @ X11 @ (k2_tarski @ X9 @ X10)))),
% 0.47/0.69      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_xboole_0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((X1) = (k2_tarski @ X0 @ X0))
% 0.47/0.69          | ((X1) = (k1_tarski @ X0))
% 0.47/0.69          | ((X1) = (k1_xboole_0))
% 0.47/0.69          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['14', '18'])).
% 0.47/0.69  thf('20', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.69  thf(t14_funct_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.69       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.69         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X25 : $i, X26 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 0.47/0.69          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.47/0.69          | ~ (v1_funct_1 @ X26)
% 0.47/0.69          | ~ (v1_relat_1 @ X26))),
% 0.47/0.69      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.47/0.69          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X0)
% 0.47/0.69          | ~ (v1_funct_1 @ X0)
% 0.47/0.69          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.69        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.69        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('eq_res', [status(thm)], ['24'])).
% 0.47/0.69  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.47/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.47/0.69        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['5', '30'])).
% 0.47/0.69  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('33', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.69  thf(t64_relat_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ A ) =>
% 0.47/0.69       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.69           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.69         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (![X24 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.47/0.69          | ((X24) = (k1_xboole_0))
% 0.47/0.69          | ~ (v1_relat_1 @ X24))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.69        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.69        | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.69  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.69  thf('38', plain, (((sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.69  thf(t60_relat_1, axiom,
% 0.47/0.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.69  thf('39', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      (![X22 : $i, X23 : $i]:
% 0.47/0.69         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.47/0.69          | ~ (v1_relat_1 @ X22))),
% 0.47/0.69      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.47/0.69          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.69  thf(t4_subset_1, axiom,
% 0.47/0.69    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.47/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.69         ((v1_relat_1 @ X27)
% 0.47/0.69          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.69  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['41', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.47/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.69  thf(t3_subset, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (![X14 : $i, X15 : $i]:
% 0.47/0.69         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.69  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.69  thf(d10_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.69  thf('49', plain,
% 0.47/0.69      (![X0 : $i, X2 : $i]:
% 0.47/0.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.69  thf('51', plain,
% 0.47/0.69      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['45', '50'])).
% 0.47/0.69  thf('52', plain, (((sk_D) = (k1_xboole_0))),
% 0.47/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.69  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.69  thf('54', plain, ($false),
% 0.47/0.69      inference('demod', [status(thm)], ['4', '38', '51', '52', '53'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
