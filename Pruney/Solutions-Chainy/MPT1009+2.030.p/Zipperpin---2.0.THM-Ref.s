%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5N0k9lXFod

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:52 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 341 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          :  662 (4100 expanded)
%              Number of equality atoms :   65 ( 284 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X7
        = ( k2_tarski @ X5 @ X6 ) )
      | ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7
        = ( k1_tarski @ X5 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
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
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != ( k1_tarski @ X21 ) )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_tarski @ ( k1_funct_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( r1_tarski @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['37','39','40','41','42','43'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['37','39','40','41','42','43'])).

thf('57',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','44','55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5N0k9lXFod
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:37:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 152 iterations in 0.060s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.18/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.49  thf(t64_funct_2, conjecture,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.18/0.49         ( m1_subset_1 @
% 0.18/0.49           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.18/0.49       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.18/0.49         ( r1_tarski @
% 0.18/0.49           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.18/0.49           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.18/0.49            ( m1_subset_1 @
% 0.18/0.49              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.18/0.49          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.18/0.49            ( r1_tarski @
% 0.18/0.49              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.18/0.49              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.18/0.49  thf('0', plain,
% 0.18/0.49      (~ (r1_tarski @ 
% 0.18/0.49          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.18/0.49          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.18/0.49         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.18/0.49          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.18/0.49           = (k9_relat_1 @ sk_D @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.18/0.49          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.49  thf(t144_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.18/0.49  thf('5', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.18/0.49          | ~ (v1_relat_1 @ X18))),
% 0.18/0.49      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc2_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.49  thf('7', plain,
% 0.18/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.18/0.49         ((v4_relat_1 @ X26 @ X27)
% 0.18/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.49  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.49  thf(d18_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      (![X16 : $i, X17 : $i]:
% 0.18/0.49         (~ (v4_relat_1 @ X16 @ X17)
% 0.18/0.49          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.18/0.49          | ~ (v1_relat_1 @ X16))),
% 0.18/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.18/0.49        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc1_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( v1_relat_1 @ C ) ))).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.18/0.49         ((v1_relat_1 @ X23)
% 0.18/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.49  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.49  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.18/0.49      inference('demod', [status(thm)], ['10', '13'])).
% 0.18/0.49  thf(t69_enumset1, axiom,
% 0.18/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.18/0.49  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.18/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.18/0.49  thf(l45_zfmisc_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.18/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.18/0.49            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.49         (((X7) = (k2_tarski @ X5 @ X6))
% 0.18/0.49          | ((X7) = (k1_tarski @ X6))
% 0.18/0.49          | ((X7) = (k1_tarski @ X5))
% 0.18/0.49          | ((X7) = (k1_xboole_0))
% 0.18/0.49          | ~ (r1_tarski @ X7 @ (k2_tarski @ X5 @ X6)))),
% 0.18/0.49      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.18/0.49  thf('17', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.18/0.49          | ((X1) = (k1_xboole_0))
% 0.18/0.49          | ((X1) = (k1_tarski @ X0))
% 0.18/0.49          | ((X1) = (k1_tarski @ X0))
% 0.18/0.49          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.49  thf('18', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((X1) = (k2_tarski @ X0 @ X0))
% 0.18/0.49          | ((X1) = (k1_tarski @ X0))
% 0.18/0.49          | ((X1) = (k1_xboole_0))
% 0.18/0.49          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['14', '18'])).
% 0.18/0.49  thf('20', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.18/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.18/0.49  thf('21', plain,
% 0.18/0.49      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.18/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.18/0.49  thf(t14_funct_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.49       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.18/0.49         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.18/0.49  thf('23', plain,
% 0.18/0.49      (![X21 : $i, X22 : $i]:
% 0.18/0.49         (((k1_relat_1 @ X22) != (k1_tarski @ X21))
% 0.18/0.49          | ((k2_relat_1 @ X22) = (k1_tarski @ (k1_funct_1 @ X22 @ X21)))
% 0.18/0.49          | ~ (v1_funct_1 @ X22)
% 0.18/0.49          | ~ (v1_relat_1 @ X22))),
% 0.18/0.49      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.18/0.49  thf('24', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.18/0.49          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.18/0.49          | ~ (v1_relat_1 @ X0)
% 0.18/0.49          | ~ (v1_funct_1 @ X0)
% 0.18/0.49          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.18/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.18/0.49  thf('25', plain,
% 0.18/0.49      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.18/0.49        | ~ (v1_funct_1 @ sk_D)
% 0.18/0.49        | ~ (v1_relat_1 @ sk_D)
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.49      inference('eq_res', [status(thm)], ['24'])).
% 0.18/0.49  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.49  thf('28', plain,
% 0.18/0.49      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.49      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.18/0.49  thf('29', plain,
% 0.18/0.49      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.18/0.49          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.49  thf('30', plain,
% 0.18/0.49      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.18/0.49        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.18/0.49  thf('31', plain,
% 0.18/0.49      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['5', '30'])).
% 0.18/0.49  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.49  thf('33', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.18/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.18/0.49  thf(t21_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( r1_tarski @
% 0.18/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.18/0.49  thf('34', plain,
% 0.18/0.49      (![X20 : $i]:
% 0.18/0.49         ((r1_tarski @ X20 @ 
% 0.18/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 0.18/0.49          | ~ (v1_relat_1 @ X20))),
% 0.18/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.18/0.49  thf(d10_xboole_0, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.49  thf('35', plain,
% 0.18/0.49      (![X0 : $i, X2 : $i]:
% 0.18/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.49  thf('36', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X0)
% 0.18/0.49          | ~ (r1_tarski @ 
% 0.18/0.49               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.18/0.49          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.49  thf('37', plain,
% 0.18/0.49      ((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.18/0.49        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_D))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_D))),
% 0.18/0.49      inference('sup-', [status(thm)], ['33', '36'])).
% 0.18/0.49  thf(t113_zfmisc_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.49  thf('38', plain,
% 0.18/0.49      (![X10 : $i, X11 : $i]:
% 0.18/0.49         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.18/0.49          | ((X10) != (k1_xboole_0)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.18/0.49  thf('39', plain,
% 0.18/0.49      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.18/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.18/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.49  thf('40', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.49  thf('41', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.18/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.18/0.49  thf('42', plain,
% 0.18/0.49      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.18/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.18/0.49  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.49  thf('44', plain, (((k1_xboole_0) = (sk_D))),
% 0.18/0.49      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.18/0.49  thf(t60_relat_1, axiom,
% 0.18/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.18/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.49  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.18/0.49  thf('46', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.18/0.49          | ~ (v1_relat_1 @ X18))),
% 0.18/0.49      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.18/0.49  thf('47', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.18/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.18/0.49      inference('sup+', [status(thm)], ['45', '46'])).
% 0.18/0.49  thf(t4_subset_1, axiom,
% 0.18/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.18/0.49  thf('48', plain,
% 0.18/0.49      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.18/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.49  thf('49', plain,
% 0.18/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.18/0.49         ((v1_relat_1 @ X23)
% 0.18/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.49  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.18/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.18/0.49  thf('51', plain,
% 0.18/0.49      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.18/0.49      inference('demod', [status(thm)], ['47', '50'])).
% 0.18/0.49  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.49  thf('53', plain,
% 0.18/0.49      (![X0 : $i, X2 : $i]:
% 0.18/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.49  thf('54', plain,
% 0.18/0.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.18/0.49  thf('55', plain,
% 0.18/0.49      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['51', '54'])).
% 0.18/0.49  thf('56', plain, (((k1_xboole_0) = (sk_D))),
% 0.18/0.49      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.18/0.49  thf('57', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.49  thf('58', plain, ($false),
% 0.18/0.49      inference('demod', [status(thm)], ['4', '44', '55', '56', '57'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
