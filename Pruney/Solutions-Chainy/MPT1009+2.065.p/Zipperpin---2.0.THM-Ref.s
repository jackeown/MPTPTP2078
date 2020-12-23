%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w0rWWeeb0d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:58 EST 2020

% Result     : Theorem 6.01s
% Output     : Refutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 200 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  729 (2528 expanded)
%              Number of equality atoms :   91 ( 217 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k1_enumset1 @ X6 @ X7 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X6 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X6 @ X7 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9
        = ( k1_tarski @ X6 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X22: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('45',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43','44','45','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w0rWWeeb0d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.01/6.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.01/6.19  % Solved by: fo/fo7.sh
% 6.01/6.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.01/6.19  % done 1184 iterations in 5.698s
% 6.01/6.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.01/6.19  % SZS output start Refutation
% 6.01/6.19  thf(sk_D_type, type, sk_D: $i).
% 6.01/6.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.01/6.19  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.01/6.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.01/6.19  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.01/6.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.01/6.19  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.01/6.19  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.01/6.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.01/6.19  thf(sk_A_type, type, sk_A: $i).
% 6.01/6.19  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.01/6.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.01/6.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.01/6.19  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.01/6.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.01/6.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.01/6.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.01/6.19  thf(sk_B_type, type, sk_B: $i).
% 6.01/6.19  thf(sk_C_type, type, sk_C: $i).
% 6.01/6.19  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.01/6.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.01/6.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.01/6.19  thf(t64_funct_2, conjecture,
% 6.01/6.19    (![A:$i,B:$i,C:$i,D:$i]:
% 6.01/6.19     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 6.01/6.19         ( m1_subset_1 @
% 6.01/6.19           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 6.01/6.19       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 6.01/6.19         ( r1_tarski @
% 6.01/6.19           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 6.01/6.19           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 6.01/6.19  thf(zf_stmt_0, negated_conjecture,
% 6.01/6.19    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.01/6.19        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 6.01/6.19            ( m1_subset_1 @
% 6.01/6.19              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 6.01/6.19          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 6.01/6.19            ( r1_tarski @
% 6.01/6.19              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 6.01/6.19              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 6.01/6.19    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 6.01/6.19  thf('0', plain,
% 6.01/6.19      (~ (r1_tarski @ 
% 6.01/6.19          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 6.01/6.19          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.01/6.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.01/6.19  thf('1', plain,
% 6.01/6.19      ((m1_subset_1 @ sk_D @ 
% 6.01/6.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.01/6.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.01/6.19  thf(redefinition_k7_relset_1, axiom,
% 6.01/6.19    (![A:$i,B:$i,C:$i,D:$i]:
% 6.01/6.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.01/6.19       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 6.01/6.19  thf('2', plain,
% 6.01/6.19      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.01/6.19         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 6.01/6.19          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 6.01/6.19      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.01/6.19  thf('3', plain,
% 6.01/6.19      (![X0 : $i]:
% 6.01/6.19         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 6.01/6.19           = (k9_relat_1 @ sk_D @ X0))),
% 6.01/6.19      inference('sup-', [status(thm)], ['1', '2'])).
% 6.01/6.19  thf('4', plain,
% 6.01/6.19      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 6.01/6.19          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.01/6.19      inference('demod', [status(thm)], ['0', '3'])).
% 6.01/6.19  thf(t144_relat_1, axiom,
% 6.01/6.19    (![A:$i,B:$i]:
% 6.01/6.19     ( ( v1_relat_1 @ B ) =>
% 6.01/6.19       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 6.01/6.19  thf('5', plain,
% 6.01/6.19      (![X20 : $i, X21 : $i]:
% 6.01/6.19         ((r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k2_relat_1 @ X20))
% 6.01/6.19          | ~ (v1_relat_1 @ X20))),
% 6.01/6.19      inference('cnf', [status(esa)], [t144_relat_1])).
% 6.01/6.19  thf('6', plain,
% 6.01/6.19      ((m1_subset_1 @ sk_D @ 
% 6.01/6.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.01/6.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.01/6.19  thf(cc2_relset_1, axiom,
% 6.01/6.19    (![A:$i,B:$i,C:$i]:
% 6.01/6.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.01/6.19       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.01/6.19  thf('7', plain,
% 6.01/6.19      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.01/6.19         ((v4_relat_1 @ X29 @ X30)
% 6.01/6.19          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 6.01/6.19      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.01/6.19  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 6.01/6.19      inference('sup-', [status(thm)], ['6', '7'])).
% 6.01/6.19  thf(d18_relat_1, axiom,
% 6.01/6.19    (![A:$i,B:$i]:
% 6.01/6.19     ( ( v1_relat_1 @ B ) =>
% 6.01/6.19       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 6.01/6.19  thf('9', plain,
% 6.01/6.19      (![X18 : $i, X19 : $i]:
% 6.01/6.19         (~ (v4_relat_1 @ X18 @ X19)
% 6.01/6.19          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 6.01/6.19          | ~ (v1_relat_1 @ X18))),
% 6.01/6.19      inference('cnf', [status(esa)], [d18_relat_1])).
% 6.01/6.19  thf('10', plain,
% 6.01/6.19      ((~ (v1_relat_1 @ sk_D)
% 6.01/6.19        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['8', '9'])).
% 6.01/6.19  thf('11', plain,
% 6.01/6.19      ((m1_subset_1 @ sk_D @ 
% 6.01/6.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.01/6.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.01/6.19  thf(cc1_relset_1, axiom,
% 6.01/6.19    (![A:$i,B:$i,C:$i]:
% 6.01/6.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.01/6.19       ( v1_relat_1 @ C ) ))).
% 6.01/6.19  thf('12', plain,
% 6.01/6.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.01/6.19         ((v1_relat_1 @ X26)
% 6.01/6.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.01/6.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.01/6.19  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 6.01/6.19      inference('sup-', [status(thm)], ['11', '12'])).
% 6.01/6.19  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 6.01/6.19      inference('demod', [status(thm)], ['10', '13'])).
% 6.01/6.19  thf(t69_enumset1, axiom,
% 6.01/6.19    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.01/6.19  thf('15', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 6.01/6.19      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.01/6.19  thf(t70_enumset1, axiom,
% 6.01/6.19    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.01/6.19  thf('16', plain,
% 6.01/6.19      (![X1 : $i, X2 : $i]:
% 6.01/6.19         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 6.01/6.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.01/6.19  thf(t142_zfmisc_1, axiom,
% 6.01/6.19    (![A:$i,B:$i,C:$i,D:$i]:
% 6.01/6.19     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 6.01/6.19       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 6.01/6.19            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 6.01/6.19            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 6.01/6.19            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 6.01/6.19            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 6.01/6.19            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 6.01/6.19  thf('17', plain,
% 6.01/6.19      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.01/6.19         (((X9) = (k1_enumset1 @ X6 @ X7 @ X8))
% 6.01/6.19          | ((X9) = (k2_tarski @ X6 @ X8))
% 6.01/6.19          | ((X9) = (k2_tarski @ X7 @ X8))
% 6.01/6.19          | ((X9) = (k2_tarski @ X6 @ X7))
% 6.01/6.19          | ((X9) = (k1_tarski @ X8))
% 6.01/6.19          | ((X9) = (k1_tarski @ X7))
% 6.01/6.19          | ((X9) = (k1_tarski @ X6))
% 6.01/6.19          | ((X9) = (k1_xboole_0))
% 6.01/6.19          | ~ (r1_tarski @ X9 @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 6.01/6.19      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 6.01/6.19  thf('18', plain,
% 6.01/6.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.01/6.19         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k1_xboole_0))
% 6.01/6.19          | ((X2) = (k1_tarski @ X1))
% 6.01/6.19          | ((X2) = (k1_tarski @ X1))
% 6.01/6.19          | ((X2) = (k1_tarski @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X1))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['16', '17'])).
% 6.01/6.19  thf('19', plain,
% 6.01/6.19      (![X1 : $i, X2 : $i]:
% 6.01/6.19         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 6.01/6.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.01/6.19  thf('20', plain,
% 6.01/6.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.01/6.19         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k1_xboole_0))
% 6.01/6.19          | ((X2) = (k1_tarski @ X1))
% 6.01/6.19          | ((X2) = (k1_tarski @ X1))
% 6.01/6.19          | ((X2) = (k1_tarski @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X1))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 6.01/6.19      inference('demod', [status(thm)], ['18', '19'])).
% 6.01/6.19  thf('21', plain,
% 6.01/6.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.01/6.19         (((X2) = (k2_tarski @ X1 @ X0))
% 6.01/6.19          | ((X2) = (k2_tarski @ X1 @ X1))
% 6.01/6.19          | ((X2) = (k1_tarski @ X0))
% 6.01/6.19          | ((X2) = (k1_tarski @ X1))
% 6.01/6.19          | ((X2) = (k1_xboole_0))
% 6.01/6.19          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 6.01/6.19      inference('simplify', [status(thm)], ['20'])).
% 6.01/6.19  thf('22', plain,
% 6.01/6.19      (![X0 : $i, X1 : $i]:
% 6.01/6.19         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 6.01/6.19          | ((X1) = (k1_xboole_0))
% 6.01/6.19          | ((X1) = (k1_tarski @ X0))
% 6.01/6.19          | ((X1) = (k1_tarski @ X0))
% 6.01/6.19          | ((X1) = (k2_tarski @ X0 @ X0))
% 6.01/6.19          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['15', '21'])).
% 6.01/6.19  thf('23', plain,
% 6.01/6.19      (![X0 : $i, X1 : $i]:
% 6.01/6.19         (((X1) = (k2_tarski @ X0 @ X0))
% 6.01/6.19          | ((X1) = (k1_tarski @ X0))
% 6.01/6.19          | ((X1) = (k1_xboole_0))
% 6.01/6.19          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 6.01/6.19      inference('simplify', [status(thm)], ['22'])).
% 6.01/6.19  thf('24', plain,
% 6.01/6.19      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['14', '23'])).
% 6.01/6.19  thf('25', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 6.01/6.19      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.01/6.19  thf('26', plain,
% 6.01/6.19      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 6.01/6.19      inference('demod', [status(thm)], ['24', '25'])).
% 6.01/6.19  thf('27', plain,
% 6.01/6.19      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('simplify', [status(thm)], ['26'])).
% 6.01/6.19  thf(t14_funct_1, axiom,
% 6.01/6.19    (![A:$i,B:$i]:
% 6.01/6.19     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.01/6.19       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 6.01/6.19         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 6.01/6.19  thf('28', plain,
% 6.01/6.19      (![X24 : $i, X25 : $i]:
% 6.01/6.19         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 6.01/6.19          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 6.01/6.19          | ~ (v1_funct_1 @ X25)
% 6.01/6.19          | ~ (v1_relat_1 @ X25))),
% 6.01/6.19      inference('cnf', [status(esa)], [t14_funct_1])).
% 6.01/6.19  thf('29', plain,
% 6.01/6.19      (![X0 : $i]:
% 6.01/6.19         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 6.01/6.19          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 6.01/6.19          | ~ (v1_relat_1 @ X0)
% 6.01/6.19          | ~ (v1_funct_1 @ X0)
% 6.01/6.19          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 6.01/6.19      inference('sup-', [status(thm)], ['27', '28'])).
% 6.01/6.19  thf('30', plain,
% 6.01/6.19      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 6.01/6.19        | ~ (v1_funct_1 @ sk_D)
% 6.01/6.19        | ~ (v1_relat_1 @ sk_D)
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('eq_res', [status(thm)], ['29'])).
% 6.01/6.19  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 6.01/6.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.01/6.19  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 6.01/6.19      inference('sup-', [status(thm)], ['11', '12'])).
% 6.01/6.19  thf('33', plain,
% 6.01/6.19      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('demod', [status(thm)], ['30', '31', '32'])).
% 6.01/6.19  thf('34', plain,
% 6.01/6.19      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 6.01/6.19          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.01/6.19      inference('demod', [status(thm)], ['0', '3'])).
% 6.01/6.19  thf('35', plain,
% 6.01/6.19      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 6.01/6.19        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['33', '34'])).
% 6.01/6.19  thf('36', plain,
% 6.01/6.19      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['5', '35'])).
% 6.01/6.19  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 6.01/6.19      inference('sup-', [status(thm)], ['11', '12'])).
% 6.01/6.19  thf('38', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 6.01/6.19      inference('demod', [status(thm)], ['36', '37'])).
% 6.01/6.19  thf(t64_relat_1, axiom,
% 6.01/6.19    (![A:$i]:
% 6.01/6.19     ( ( v1_relat_1 @ A ) =>
% 6.01/6.19       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 6.01/6.19           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.01/6.19         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 6.01/6.19  thf('39', plain,
% 6.01/6.19      (![X23 : $i]:
% 6.01/6.19         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 6.01/6.19          | ((X23) = (k1_xboole_0))
% 6.01/6.19          | ~ (v1_relat_1 @ X23))),
% 6.01/6.19      inference('cnf', [status(esa)], [t64_relat_1])).
% 6.01/6.19  thf('40', plain,
% 6.01/6.19      ((((k1_xboole_0) != (k1_xboole_0))
% 6.01/6.19        | ~ (v1_relat_1 @ sk_D)
% 6.01/6.19        | ((sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('sup-', [status(thm)], ['38', '39'])).
% 6.01/6.19  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 6.01/6.19      inference('sup-', [status(thm)], ['11', '12'])).
% 6.01/6.19  thf('42', plain,
% 6.01/6.19      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 6.01/6.19      inference('demod', [status(thm)], ['40', '41'])).
% 6.01/6.19  thf('43', plain, (((sk_D) = (k1_xboole_0))),
% 6.01/6.19      inference('simplify', [status(thm)], ['42'])).
% 6.01/6.19  thf(t150_relat_1, axiom,
% 6.01/6.19    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 6.01/6.19  thf('44', plain,
% 6.01/6.19      (![X22 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 6.01/6.19      inference('cnf', [status(esa)], [t150_relat_1])).
% 6.01/6.19  thf('45', plain, (((sk_D) = (k1_xboole_0))),
% 6.01/6.19      inference('simplify', [status(thm)], ['42'])).
% 6.01/6.19  thf(t4_subset_1, axiom,
% 6.01/6.19    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.01/6.19  thf('46', plain,
% 6.01/6.19      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 6.01/6.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.01/6.19  thf(t3_subset, axiom,
% 6.01/6.19    (![A:$i,B:$i]:
% 6.01/6.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.01/6.19  thf('47', plain,
% 6.01/6.19      (![X12 : $i, X13 : $i]:
% 6.01/6.19         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 6.01/6.19      inference('cnf', [status(esa)], [t3_subset])).
% 6.01/6.19  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.01/6.19      inference('sup-', [status(thm)], ['46', '47'])).
% 6.01/6.19  thf('49', plain, ($false),
% 6.01/6.19      inference('demod', [status(thm)], ['4', '43', '44', '45', '48'])).
% 6.01/6.19  
% 6.01/6.19  % SZS output end Refutation
% 6.01/6.19  
% 6.01/6.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
