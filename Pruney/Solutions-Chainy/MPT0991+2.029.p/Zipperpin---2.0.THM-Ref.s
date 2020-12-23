%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vlXUM4cBbg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:34 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  663 (1737 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X24 @ X22 @ X22 @ X23 @ X25 @ X21 ) )
      | ( v2_funct_1 @ X25 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','36','38'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('42',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('43',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('44',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vlXUM4cBbg
% 0.17/0.39  % Computer   : n006.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 09:16:23 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 175 iterations in 0.116s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.43/0.62  thf(t37_funct_2, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62            ( ?[D:$i]:
% 0.43/0.62              ( ( r2_relset_1 @
% 0.43/0.62                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.62                  ( k6_partfun1 @ A ) ) & 
% 0.43/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.43/0.62                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.43/0.62            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62               ( ?[D:$i]:
% 0.43/0.62                 ( ( r2_relset_1 @
% 0.43/0.62                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.62                     ( k6_partfun1 @ A ) ) & 
% 0.43/0.62                   ( m1_subset_1 @
% 0.43/0.62                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.43/0.62                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.43/0.62               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.43/0.62  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t3_subset, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i]:
% 0.43/0.62         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.62  thf('3', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.62        (k6_partfun1 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(redefinition_k6_partfun1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.43/0.62  thf('5', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.62        (k6_relat_1 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_k1_partfun1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.62     ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.62         ( v1_funct_1 @ F ) & 
% 0.43/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.43/0.62       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.43/0.62         ( m1_subset_1 @
% 0.43/0.62           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.43/0.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_1 @ X15)
% 0.43/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.43/0.62          | (m1_subset_1 @ (k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15) @ 
% 0.43/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X17))))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.62  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.62          | ~ (v1_funct_1 @ X1))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((~ (v1_funct_1 @ sk_D)
% 0.43/0.62        | (m1_subset_1 @ 
% 0.43/0.62           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '12'])).
% 0.43/0.62  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      ((m1_subset_1 @ 
% 0.43/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf(redefinition_r2_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.43/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.43/0.62          | ((X8) = (X11))
% 0.43/0.62          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.62             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.43/0.62          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.43/0.62        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.62            = (k6_relat_1 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['6', '17'])).
% 0.43/0.62  thf(dt_k6_partfun1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( m1_subset_1 @
% 0.43/0.62         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.43/0.62       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X19 : $i]:
% 0.43/0.62         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.43/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.43/0.62  thf('20', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X19 : $i]:
% 0.43/0.62         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.43/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.43/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.62         = (k6_relat_1 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t26_funct_2, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.43/0.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.43/0.62           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.43/0.62             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.43/0.62               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.62         (~ (v1_funct_1 @ X21)
% 0.43/0.62          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.43/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.43/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X24 @ X22 @ X22 @ X23 @ X25 @ X21))
% 0.43/0.62          | (v2_funct_1 @ X25)
% 0.43/0.62          | ((X23) = (k1_xboole_0))
% 0.43/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.43/0.62          | ~ (v1_funct_2 @ X25 @ X24 @ X22)
% 0.43/0.62          | ~ (v1_funct_1 @ X25))),
% 0.43/0.62      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_funct_1 @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.43/0.62          | ((sk_A) = (k1_xboole_0))
% 0.43/0.62          | (v2_funct_1 @ X0)
% 0.43/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.43/0.62          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ sk_D))),
% 0.43/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.62  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_funct_1 @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.43/0.62          | ((sk_A) = (k1_xboole_0))
% 0.43/0.62          | (v2_funct_1 @ X0)
% 0.43/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.43/0.62      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.43/0.62        | (v2_funct_1 @ sk_C)
% 0.43/0.62        | ((sk_A) = (k1_xboole_0))
% 0.43/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '28'])).
% 0.43/0.62  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.43/0.62  thf('30', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('34', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.43/0.62  thf('35', plain, (~ (v2_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('clc', [status(thm)], ['34', '35'])).
% 0.43/0.62  thf(t113_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]:
% 0.43/0.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.43/0.62  thf('39', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.43/0.62      inference('demod', [status(thm)], ['3', '36', '38'])).
% 0.43/0.62  thf(t3_xboole_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.43/0.62  thf('41', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.43/0.62  thf('42', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.43/0.62  thf('43', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.43/0.62  thf('44', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.43/0.62  thf('45', plain, ($false),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '41', '44'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
