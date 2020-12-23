%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5Rf2AACNj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:20 EST 2020

% Result     : Theorem 8.82s
% Output     : Refutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 591 expanded)
%              Number of leaves         :   48 ( 190 expanded)
%              Depth                    :   20
%              Number of atoms          : 1469 (10414 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
      = ( k5_relat_1 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('16',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('17',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( $true
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('48',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('49',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','74'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('76',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('80',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','74'])).

thf('95',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['79','82','93','94','95','96','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('104',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('106',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ X31 )
       != X30 )
      | ( v2_funct_2 @ X31 @ X30 )
      | ~ ( v5_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('107',plain,(
    ! [X31: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
      | ( v2_funct_2 @ X31 @ ( k2_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('112',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('114',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('116',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['55','116'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','117'])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','123'])).

thf('125',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('127',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('139',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('140',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['138','139'])).

thf('141',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['137','140'])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['124','141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5Rf2AACNj
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.82/9.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.82/9.03  % Solved by: fo/fo7.sh
% 8.82/9.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.82/9.03  % done 3660 iterations in 8.552s
% 8.82/9.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.82/9.03  % SZS output start Refutation
% 8.82/9.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.82/9.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.82/9.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.82/9.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.82/9.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.82/9.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.82/9.03  thf(sk_D_type, type, sk_D: $i).
% 8.82/9.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.82/9.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.82/9.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.82/9.03  thf(sk_A_type, type, sk_A: $i).
% 8.82/9.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.82/9.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 8.82/9.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.82/9.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 8.82/9.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.82/9.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.82/9.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.82/9.03  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 8.82/9.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.82/9.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 8.82/9.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.82/9.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.82/9.03  thf(sk_C_type, type, sk_C: $i).
% 8.82/9.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.82/9.03  thf(sk_B_type, type, sk_B: $i).
% 8.82/9.03  thf(t29_funct_2, conjecture,
% 8.82/9.03    (![A:$i,B:$i,C:$i]:
% 8.82/9.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.82/9.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/9.03       ( ![D:$i]:
% 8.82/9.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.82/9.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.82/9.03           ( ( r2_relset_1 @
% 8.82/9.03               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.82/9.03               ( k6_partfun1 @ A ) ) =>
% 8.82/9.03             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 8.82/9.03  thf(zf_stmt_0, negated_conjecture,
% 8.82/9.03    (~( ![A:$i,B:$i,C:$i]:
% 8.82/9.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.82/9.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/9.03          ( ![D:$i]:
% 8.82/9.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.82/9.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.82/9.03              ( ( r2_relset_1 @
% 8.82/9.03                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.82/9.03                  ( k6_partfun1 @ A ) ) =>
% 8.82/9.03                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 8.82/9.03    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 8.82/9.03  thf('0', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('1', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(redefinition_k1_partfun1, axiom,
% 8.82/9.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.82/9.03     ( ( ( v1_funct_1 @ E ) & 
% 8.82/9.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.82/9.03         ( v1_funct_1 @ F ) & 
% 8.82/9.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.82/9.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 8.82/9.03  thf('2', plain,
% 8.82/9.03      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 8.82/9.03          | ~ (v1_funct_1 @ X40)
% 8.82/9.03          | ~ (v1_funct_1 @ X43)
% 8.82/9.03          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 8.82/9.03          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 8.82/9.03              = (k5_relat_1 @ X40 @ X43)))),
% 8.82/9.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 8.82/9.03  thf('3', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.82/9.03            = (k5_relat_1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0)
% 8.82/9.03          | ~ (v1_funct_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['1', '2'])).
% 8.82/9.03  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('5', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.82/9.03            = (k5_relat_1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0))),
% 8.82/9.03      inference('demod', [status(thm)], ['3', '4'])).
% 8.82/9.03  thf('6', plain,
% 8.82/9.03      ((~ (v1_funct_1 @ sk_C)
% 8.82/9.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 8.82/9.03            = (k5_relat_1 @ sk_C @ sk_C)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['0', '5'])).
% 8.82/9.03  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('8', plain,
% 8.82/9.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 8.82/9.03         = (k5_relat_1 @ sk_C @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['6', '7'])).
% 8.82/9.03  thf(l13_xboole_0, axiom,
% 8.82/9.03    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.82/9.03  thf('9', plain,
% 8.82/9.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.82/9.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 8.82/9.03  thf(fc4_zfmisc_1, axiom,
% 8.82/9.03    (![A:$i,B:$i]:
% 8.82/9.03     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 8.82/9.03  thf('10', plain,
% 8.82/9.03      (![X8 : $i, X9 : $i]:
% 8.82/9.03         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 8.82/9.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 8.82/9.03  thf('11', plain,
% 8.82/9.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.82/9.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 8.82/9.03  thf('12', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i]:
% 8.82/9.03         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['10', '11'])).
% 8.82/9.03  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 8.82/9.03  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.82/9.03      inference('cnf', [status(esa)], [t81_relat_1])).
% 8.82/9.03  thf(redefinition_k6_partfun1, axiom,
% 8.82/9.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.82/9.03  thf('14', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 8.82/9.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.82/9.03  thf('15', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.82/9.03      inference('demod', [status(thm)], ['13', '14'])).
% 8.82/9.03  thf(dt_k6_partfun1, axiom,
% 8.82/9.03    (![A:$i]:
% 8.82/9.03     ( ( m1_subset_1 @
% 8.82/9.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 8.82/9.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 8.82/9.03  thf('16', plain,
% 8.82/9.03      (![X39 : $i]:
% 8.82/9.03         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 8.82/9.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 8.82/9.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 8.82/9.03  thf('17', plain,
% 8.82/9.03      ((m1_subset_1 @ k1_xboole_0 @ 
% 8.82/9.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 8.82/9.03      inference('sup+', [status(thm)], ['15', '16'])).
% 8.82/9.03  thf('18', plain,
% 8.82/9.03      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.82/9.03        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 8.82/9.03      inference('sup+', [status(thm)], ['12', '17'])).
% 8.82/9.03  thf(d10_xboole_0, axiom,
% 8.82/9.03    (![A:$i,B:$i]:
% 8.82/9.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.82/9.03  thf('19', plain,
% 8.82/9.03      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 8.82/9.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.82/9.03  thf('20', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 8.82/9.03      inference('simplify', [status(thm)], ['19'])).
% 8.82/9.03  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 8.82/9.03  thf('21', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 8.82/9.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 8.82/9.03  thf(t69_xboole_1, axiom,
% 8.82/9.03    (![A:$i,B:$i]:
% 8.82/9.03     ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.82/9.03       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 8.82/9.03  thf('22', plain,
% 8.82/9.03      (![X6 : $i, X7 : $i]:
% 8.82/9.03         (~ (r1_xboole_0 @ X6 @ X7)
% 8.82/9.03          | ~ (r1_tarski @ X6 @ X7)
% 8.82/9.03          | (v1_xboole_0 @ X6))),
% 8.82/9.03      inference('cnf', [status(esa)], [t69_xboole_1])).
% 8.82/9.03  thf('23', plain,
% 8.82/9.03      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 8.82/9.03      inference('sup-', [status(thm)], ['21', '22'])).
% 8.82/9.03  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.82/9.03      inference('sup-', [status(thm)], ['20', '23'])).
% 8.82/9.03  thf('25', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 8.82/9.03      inference('demod', [status(thm)], ['18', '24'])).
% 8.82/9.03  thf('26', plain,
% 8.82/9.03      (![X0 : $i]:
% 8.82/9.03         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.82/9.03          | ~ (v1_xboole_0 @ X0))),
% 8.82/9.03      inference('sup+', [status(thm)], ['9', '25'])).
% 8.82/9.03  thf('27', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i]:
% 8.82/9.03         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['10', '11'])).
% 8.82/9.03  thf('28', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(dt_k1_partfun1, axiom,
% 8.82/9.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.82/9.03     ( ( ( v1_funct_1 @ E ) & 
% 8.82/9.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.82/9.03         ( v1_funct_1 @ F ) & 
% 8.82/9.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.82/9.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.82/9.03         ( m1_subset_1 @
% 8.82/9.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.82/9.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 8.82/9.03  thf('29', plain,
% 8.82/9.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.82/9.03          | ~ (v1_funct_1 @ X32)
% 8.82/9.03          | ~ (v1_funct_1 @ X35)
% 8.82/9.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 8.82/9.03          | (v1_funct_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)))),
% 8.82/9.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.82/9.03  thf('30', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0)
% 8.82/9.03          | ~ (v1_funct_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['28', '29'])).
% 8.82/9.03  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('32', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0))),
% 8.82/9.03      inference('demod', [status(thm)], ['30', '31'])).
% 8.82/9.03  thf('33', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.82/9.03          | ~ (v1_xboole_0 @ X1)
% 8.82/9.03          | ~ (v1_funct_1 @ X2)
% 8.82/9.03          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['27', '32'])).
% 8.82/9.03  thf('34', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         (~ (v1_xboole_0 @ X0)
% 8.82/9.03          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 8.82/9.03          | ~ (v1_funct_1 @ X0)
% 8.82/9.03          | ~ (v1_xboole_0 @ X2))),
% 8.82/9.03      inference('sup-', [status(thm)], ['26', '33'])).
% 8.82/9.03  thf('35', plain,
% 8.82/9.03      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 8.82/9.03        | ~ (v1_xboole_0 @ sk_A)
% 8.82/9.03        | ~ (v1_funct_1 @ sk_C)
% 8.82/9.03        | ~ (v1_xboole_0 @ sk_C))),
% 8.82/9.03      inference('sup+', [status(thm)], ['8', '34'])).
% 8.82/9.03  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('37', plain,
% 8.82/9.03      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 8.82/9.03        | ~ (v1_xboole_0 @ sk_A)
% 8.82/9.03        | ~ (v1_xboole_0 @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['35', '36'])).
% 8.82/9.03  thf('38', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('39', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0))),
% 8.82/9.03      inference('demod', [status(thm)], ['30', '31'])).
% 8.82/9.03  thf('40', plain,
% 8.82/9.03      ((~ (v1_funct_1 @ sk_C)
% 8.82/9.03        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['38', '39'])).
% 8.82/9.03  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('42', plain,
% 8.82/9.03      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['40', '41'])).
% 8.82/9.03  thf('43', plain,
% 8.82/9.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 8.82/9.03         = (k5_relat_1 @ sk_C @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['6', '7'])).
% 8.82/9.03  thf('44', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['42', '43'])).
% 8.82/9.03  thf('45', plain, (($true | ~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 8.82/9.03      inference('demod', [status(thm)], ['37', '44'])).
% 8.82/9.03  thf('46', plain,
% 8.82/9.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.82/9.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 8.82/9.03  thf('47', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.82/9.03      inference('demod', [status(thm)], ['13', '14'])).
% 8.82/9.03  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 8.82/9.03  thf('48', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 8.82/9.03      inference('cnf', [status(esa)], [t52_funct_1])).
% 8.82/9.03  thf('49', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 8.82/9.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.82/9.03  thf('50', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 8.82/9.03      inference('demod', [status(thm)], ['48', '49'])).
% 8.82/9.03  thf('51', plain, ((v2_funct_1 @ k1_xboole_0)),
% 8.82/9.03      inference('sup+', [status(thm)], ['47', '50'])).
% 8.82/9.03  thf('52', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 8.82/9.03      inference('sup+', [status(thm)], ['46', '51'])).
% 8.82/9.03  thf('53', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('54', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.82/9.03      inference('split', [status(esa)], ['53'])).
% 8.82/9.03  thf('55', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['52', '54'])).
% 8.82/9.03  thf('56', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('57', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.82/9.03            = (k5_relat_1 @ sk_C @ X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.82/9.03          | ~ (v1_funct_1 @ X0))),
% 8.82/9.03      inference('demod', [status(thm)], ['3', '4'])).
% 8.82/9.03  thf('58', plain,
% 8.82/9.03      ((~ (v1_funct_1 @ sk_D)
% 8.82/9.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.82/9.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['56', '57'])).
% 8.82/9.03  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('60', plain,
% 8.82/9.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 8.82/9.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.82/9.03        (k6_partfun1 @ sk_A))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('61', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('62', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('63', plain,
% 8.82/9.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.82/9.03          | ~ (v1_funct_1 @ X32)
% 8.82/9.03          | ~ (v1_funct_1 @ X35)
% 8.82/9.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 8.82/9.03          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 8.82/9.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 8.82/9.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.82/9.03  thf('64', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.82/9.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.82/9.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.82/9.03          | ~ (v1_funct_1 @ X1)
% 8.82/9.03          | ~ (v1_funct_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['62', '63'])).
% 8.82/9.03  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('66', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.82/9.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.82/9.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.82/9.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.82/9.03          | ~ (v1_funct_1 @ X1))),
% 8.82/9.03      inference('demod', [status(thm)], ['64', '65'])).
% 8.82/9.03  thf('67', plain,
% 8.82/9.03      ((~ (v1_funct_1 @ sk_D)
% 8.82/9.03        | (m1_subset_1 @ 
% 8.82/9.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.82/9.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.82/9.03      inference('sup-', [status(thm)], ['61', '66'])).
% 8.82/9.03  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('69', plain,
% 8.82/9.03      ((m1_subset_1 @ 
% 8.82/9.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.82/9.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.82/9.03      inference('demod', [status(thm)], ['67', '68'])).
% 8.82/9.03  thf(redefinition_r2_relset_1, axiom,
% 8.82/9.03    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/9.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.82/9.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/9.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 8.82/9.03  thf('70', plain,
% 8.82/9.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 8.82/9.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 8.82/9.03          | ((X26) = (X29))
% 8.82/9.03          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 8.82/9.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 8.82/9.03  thf('71', plain,
% 8.82/9.03      (![X0 : $i]:
% 8.82/9.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 8.82/9.03             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 8.82/9.03          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.82/9.03      inference('sup-', [status(thm)], ['69', '70'])).
% 8.82/9.03  thf('72', plain,
% 8.82/9.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 8.82/9.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 8.82/9.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.82/9.03            = (k6_partfun1 @ sk_A)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['60', '71'])).
% 8.82/9.03  thf('73', plain,
% 8.82/9.03      (![X39 : $i]:
% 8.82/9.03         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 8.82/9.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 8.82/9.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 8.82/9.03  thf('74', plain,
% 8.82/9.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.82/9.03         = (k6_partfun1 @ sk_A))),
% 8.82/9.03      inference('demod', [status(thm)], ['72', '73'])).
% 8.82/9.03  thf('75', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 8.82/9.03      inference('demod', [status(thm)], ['58', '59', '74'])).
% 8.82/9.03  thf(t45_relat_1, axiom,
% 8.82/9.03    (![A:$i]:
% 8.82/9.03     ( ( v1_relat_1 @ A ) =>
% 8.82/9.03       ( ![B:$i]:
% 8.82/9.03         ( ( v1_relat_1 @ B ) =>
% 8.82/9.03           ( r1_tarski @
% 8.82/9.03             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 8.82/9.03  thf('76', plain,
% 8.82/9.03      (![X18 : $i, X19 : $i]:
% 8.82/9.03         (~ (v1_relat_1 @ X18)
% 8.82/9.03          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 8.82/9.03             (k2_relat_1 @ X18))
% 8.82/9.03          | ~ (v1_relat_1 @ X19))),
% 8.82/9.03      inference('cnf', [status(esa)], [t45_relat_1])).
% 8.82/9.03  thf('77', plain,
% 8.82/9.03      (![X1 : $i, X3 : $i]:
% 8.82/9.03         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 8.82/9.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.82/9.03  thf('78', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i]:
% 8.82/9.03         (~ (v1_relat_1 @ X1)
% 8.82/9.03          | ~ (v1_relat_1 @ X0)
% 8.82/9.03          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 8.82/9.03               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 8.82/9.03          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 8.82/9.03      inference('sup-', [status(thm)], ['76', '77'])).
% 8.82/9.03  thf('79', plain,
% 8.82/9.03      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 8.82/9.03           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 8.82/9.03        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 8.82/9.03        | ~ (v1_relat_1 @ sk_D)
% 8.82/9.03        | ~ (v1_relat_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['75', '78'])).
% 8.82/9.03  thf(t71_relat_1, axiom,
% 8.82/9.03    (![A:$i]:
% 8.82/9.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.82/9.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.82/9.03  thf('80', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 8.82/9.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.82/9.03  thf('81', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 8.82/9.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.82/9.03  thf('82', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 8.82/9.03      inference('demod', [status(thm)], ['80', '81'])).
% 8.82/9.03  thf('83', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(cc2_relset_1, axiom,
% 8.82/9.03    (![A:$i,B:$i,C:$i]:
% 8.82/9.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.82/9.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.82/9.03  thf('84', plain,
% 8.82/9.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.82/9.03         ((v5_relat_1 @ X23 @ X25)
% 8.82/9.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 8.82/9.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.82/9.03  thf('85', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 8.82/9.03      inference('sup-', [status(thm)], ['83', '84'])).
% 8.82/9.03  thf(d19_relat_1, axiom,
% 8.82/9.03    (![A:$i,B:$i]:
% 8.82/9.03     ( ( v1_relat_1 @ B ) =>
% 8.82/9.03       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.82/9.03  thf('86', plain,
% 8.82/9.03      (![X14 : $i, X15 : $i]:
% 8.82/9.03         (~ (v5_relat_1 @ X14 @ X15)
% 8.82/9.03          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 8.82/9.03          | ~ (v1_relat_1 @ X14))),
% 8.82/9.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.82/9.03  thf('87', plain,
% 8.82/9.03      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 8.82/9.03      inference('sup-', [status(thm)], ['85', '86'])).
% 8.82/9.03  thf('88', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(cc2_relat_1, axiom,
% 8.82/9.03    (![A:$i]:
% 8.82/9.03     ( ( v1_relat_1 @ A ) =>
% 8.82/9.03       ( ![B:$i]:
% 8.82/9.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.82/9.03  thf('89', plain,
% 8.82/9.03      (![X12 : $i, X13 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 8.82/9.03          | (v1_relat_1 @ X12)
% 8.82/9.03          | ~ (v1_relat_1 @ X13))),
% 8.82/9.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.82/9.03  thf('90', plain,
% 8.82/9.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 8.82/9.03      inference('sup-', [status(thm)], ['88', '89'])).
% 8.82/9.03  thf(fc6_relat_1, axiom,
% 8.82/9.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.82/9.03  thf('91', plain,
% 8.82/9.03      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 8.82/9.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.82/9.03  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 8.82/9.03      inference('demod', [status(thm)], ['90', '91'])).
% 8.82/9.03  thf('93', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 8.82/9.03      inference('demod', [status(thm)], ['87', '92'])).
% 8.82/9.03  thf('94', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 8.82/9.03      inference('demod', [status(thm)], ['58', '59', '74'])).
% 8.82/9.03  thf('95', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 8.82/9.03      inference('demod', [status(thm)], ['80', '81'])).
% 8.82/9.03  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 8.82/9.03      inference('demod', [status(thm)], ['90', '91'])).
% 8.82/9.03  thf('97', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('98', plain,
% 8.82/9.03      (![X12 : $i, X13 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 8.82/9.03          | (v1_relat_1 @ X12)
% 8.82/9.03          | ~ (v1_relat_1 @ X13))),
% 8.82/9.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.82/9.03  thf('99', plain,
% 8.82/9.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['97', '98'])).
% 8.82/9.03  thf('100', plain,
% 8.82/9.03      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 8.82/9.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.82/9.03  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 8.82/9.03      inference('demod', [status(thm)], ['99', '100'])).
% 8.82/9.03  thf('102', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 8.82/9.03      inference('demod', [status(thm)],
% 8.82/9.03                ['79', '82', '93', '94', '95', '96', '101'])).
% 8.82/9.03  thf('103', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 8.82/9.03      inference('simplify', [status(thm)], ['19'])).
% 8.82/9.03  thf('104', plain,
% 8.82/9.03      (![X14 : $i, X15 : $i]:
% 8.82/9.03         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 8.82/9.03          | (v5_relat_1 @ X14 @ X15)
% 8.82/9.03          | ~ (v1_relat_1 @ X14))),
% 8.82/9.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.82/9.03  thf('105', plain,
% 8.82/9.03      (![X0 : $i]:
% 8.82/9.03         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 8.82/9.03      inference('sup-', [status(thm)], ['103', '104'])).
% 8.82/9.03  thf(d3_funct_2, axiom,
% 8.82/9.03    (![A:$i,B:$i]:
% 8.82/9.03     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 8.82/9.03       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 8.82/9.03  thf('106', plain,
% 8.82/9.03      (![X30 : $i, X31 : $i]:
% 8.82/9.03         (((k2_relat_1 @ X31) != (X30))
% 8.82/9.03          | (v2_funct_2 @ X31 @ X30)
% 8.82/9.03          | ~ (v5_relat_1 @ X31 @ X30)
% 8.82/9.03          | ~ (v1_relat_1 @ X31))),
% 8.82/9.03      inference('cnf', [status(esa)], [d3_funct_2])).
% 8.82/9.03  thf('107', plain,
% 8.82/9.03      (![X31 : $i]:
% 8.82/9.03         (~ (v1_relat_1 @ X31)
% 8.82/9.03          | ~ (v5_relat_1 @ X31 @ (k2_relat_1 @ X31))
% 8.82/9.03          | (v2_funct_2 @ X31 @ (k2_relat_1 @ X31)))),
% 8.82/9.03      inference('simplify', [status(thm)], ['106'])).
% 8.82/9.03  thf('108', plain,
% 8.82/9.03      (![X0 : $i]:
% 8.82/9.03         (~ (v1_relat_1 @ X0)
% 8.82/9.03          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 8.82/9.03          | ~ (v1_relat_1 @ X0))),
% 8.82/9.03      inference('sup-', [status(thm)], ['105', '107'])).
% 8.82/9.03  thf('109', plain,
% 8.82/9.03      (![X0 : $i]:
% 8.82/9.03         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 8.82/9.03      inference('simplify', [status(thm)], ['108'])).
% 8.82/9.03  thf('110', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 8.82/9.03      inference('sup+', [status(thm)], ['102', '109'])).
% 8.82/9.03  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 8.82/9.03      inference('demod', [status(thm)], ['90', '91'])).
% 8.82/9.03  thf('112', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 8.82/9.03      inference('demod', [status(thm)], ['110', '111'])).
% 8.82/9.03  thf('113', plain,
% 8.82/9.03      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 8.82/9.03      inference('split', [status(esa)], ['53'])).
% 8.82/9.03  thf('114', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 8.82/9.03      inference('sup-', [status(thm)], ['112', '113'])).
% 8.82/9.03  thf('115', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 8.82/9.03      inference('split', [status(esa)], ['53'])).
% 8.82/9.03  thf('116', plain, (~ ((v2_funct_1 @ sk_C))),
% 8.82/9.03      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 8.82/9.03  thf('117', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.82/9.03      inference('simpl_trail', [status(thm)], ['55', '116'])).
% 8.82/9.03  thf('118', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 8.82/9.03      inference('clc', [status(thm)], ['45', '117'])).
% 8.82/9.03  thf('119', plain,
% 8.82/9.03      (![X8 : $i, X9 : $i]:
% 8.82/9.03         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 8.82/9.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 8.82/9.03  thf('120', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(cc1_subset_1, axiom,
% 8.82/9.03    (![A:$i]:
% 8.82/9.03     ( ( v1_xboole_0 @ A ) =>
% 8.82/9.03       ( ![B:$i]:
% 8.82/9.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 8.82/9.03  thf('121', plain,
% 8.82/9.03      (![X10 : $i, X11 : $i]:
% 8.82/9.03         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 8.82/9.03          | (v1_xboole_0 @ X10)
% 8.82/9.03          | ~ (v1_xboole_0 @ X11))),
% 8.82/9.03      inference('cnf', [status(esa)], [cc1_subset_1])).
% 8.82/9.03  thf('122', plain,
% 8.82/9.03      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['120', '121'])).
% 8.82/9.03  thf('123', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['119', '122'])).
% 8.82/9.03  thf('124', plain, (~ (v1_xboole_0 @ sk_A)),
% 8.82/9.03      inference('clc', [status(thm)], ['118', '123'])).
% 8.82/9.03  thf('125', plain,
% 8.82/9.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.82/9.03         = (k6_partfun1 @ sk_A))),
% 8.82/9.03      inference('demod', [status(thm)], ['72', '73'])).
% 8.82/9.03  thf('126', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf(t26_funct_2, axiom,
% 8.82/9.03    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/9.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.82/9.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/9.03       ( ![E:$i]:
% 8.82/9.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 8.82/9.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.82/9.03           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 8.82/9.03             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 8.82/9.03               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 8.82/9.03  thf('127', plain,
% 8.82/9.03      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 8.82/9.03         (~ (v1_funct_1 @ X47)
% 8.82/9.03          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 8.82/9.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 8.82/9.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 8.82/9.03          | (v2_funct_1 @ X51)
% 8.82/9.03          | ((X49) = (k1_xboole_0))
% 8.82/9.03          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 8.82/9.03          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 8.82/9.03          | ~ (v1_funct_1 @ X51))),
% 8.82/9.03      inference('cnf', [status(esa)], [t26_funct_2])).
% 8.82/9.03  thf('128', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i]:
% 8.82/9.03         (~ (v1_funct_1 @ X0)
% 8.82/9.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.82/9.03          | ((sk_A) = (k1_xboole_0))
% 8.82/9.03          | (v2_funct_1 @ X0)
% 8.82/9.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 8.82/9.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 8.82/9.03          | ~ (v1_funct_1 @ sk_D))),
% 8.82/9.03      inference('sup-', [status(thm)], ['126', '127'])).
% 8.82/9.03  thf('129', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('131', plain,
% 8.82/9.03      (![X0 : $i, X1 : $i]:
% 8.82/9.03         (~ (v1_funct_1 @ X0)
% 8.82/9.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.82/9.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.82/9.03          | ((sk_A) = (k1_xboole_0))
% 8.82/9.03          | (v2_funct_1 @ X0)
% 8.82/9.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 8.82/9.03      inference('demod', [status(thm)], ['128', '129', '130'])).
% 8.82/9.03  thf('132', plain,
% 8.82/9.03      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 8.82/9.03        | (v2_funct_1 @ sk_C)
% 8.82/9.03        | ((sk_A) = (k1_xboole_0))
% 8.82/9.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 8.82/9.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 8.82/9.03        | ~ (v1_funct_1 @ sk_C))),
% 8.82/9.03      inference('sup-', [status(thm)], ['125', '131'])).
% 8.82/9.03  thf('133', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 8.82/9.03      inference('demod', [status(thm)], ['48', '49'])).
% 8.82/9.03  thf('134', plain,
% 8.82/9.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('135', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.03  thf('137', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 8.82/9.03      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 8.82/9.03  thf('138', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.82/9.03      inference('split', [status(esa)], ['53'])).
% 8.82/9.03  thf('139', plain, (~ ((v2_funct_1 @ sk_C))),
% 8.82/9.03      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 8.82/9.03  thf('140', plain, (~ (v2_funct_1 @ sk_C)),
% 8.82/9.03      inference('simpl_trail', [status(thm)], ['138', '139'])).
% 8.82/9.03  thf('141', plain, (((sk_A) = (k1_xboole_0))),
% 8.82/9.03      inference('clc', [status(thm)], ['137', '140'])).
% 8.82/9.03  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.82/9.03      inference('sup-', [status(thm)], ['20', '23'])).
% 8.82/9.03  thf('143', plain, ($false),
% 8.82/9.03      inference('demod', [status(thm)], ['124', '141', '142'])).
% 8.82/9.03  
% 8.82/9.03  % SZS output end Refutation
% 8.82/9.03  
% 8.82/9.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
