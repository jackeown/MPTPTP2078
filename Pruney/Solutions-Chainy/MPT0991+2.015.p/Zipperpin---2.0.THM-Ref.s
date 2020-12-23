%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MuQg4R9o3F

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:32 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 105 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  675 (1746 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X16 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_relset_1 @ X8 @ X9 @ X7 @ X10 ) ) ),
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
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X23 @ X21 @ X21 @ X22 @ X24 @ X20 ) )
      | ( v2_funct_1 @ X24 )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','36','37'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('39',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MuQg4R9o3F
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:07:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 234 iterations in 0.203s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(t37_funct_2, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63            ( ?[D:$i]:
% 0.46/0.63              ( ( r2_relset_1 @
% 0.46/0.63                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.63                  ( k6_partfun1 @ A ) ) & 
% 0.46/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.46/0.63                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.46/0.63            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63               ( ?[D:$i]:
% 0.46/0.63                 ( ( r2_relset_1 @
% 0.46/0.63                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.63                     ( k6_partfun1 @ A ) ) & 
% 0.46/0.63                   ( m1_subset_1 @
% 0.46/0.63                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.46/0.63                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.46/0.63               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.46/0.63  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc3_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.63         (~ (v1_xboole_0 @ X4)
% 0.46/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X6)))
% 0.46/0.63          | (v1_xboole_0 @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.46/0.63  thf('3', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.63        (k6_partfun1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.63  thf('5', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.63        (k6_relat_1 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k1_partfun1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( v1_funct_1 @ F ) & 
% 0.46/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.63       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.63         ( m1_subset_1 @
% 0.46/0.63           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_funct_1 @ X14)
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.63          | (m1_subset_1 @ (k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X16))))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.63          | ~ (v1_funct_1 @ X1))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.63        | (m1_subset_1 @ 
% 0.46/0.63           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '12'])).
% 0.46/0.63  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((m1_subset_1 @ 
% 0.46/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.46/0.63          | ((X7) = (X10))
% 0.46/0.63          | ~ (r2_relset_1 @ X8 @ X9 @ X7 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.46/0.63          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.63        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.63            = (k6_relat_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '17'])).
% 0.46/0.63  thf(dt_k6_partfun1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( m1_subset_1 @
% 0.46/0.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.46/0.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X18 : $i]:
% 0.46/0.63         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.46/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.46/0.63  thf('20', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X18 : $i]:
% 0.46/0.63         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 0.46/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.46/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.63         = (k6_relat_1 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['18', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t26_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ![E:$i]:
% 0.46/0.63         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.46/0.63             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.63           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.46/0.63             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.63               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X20)
% 0.46/0.63          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.46/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X23 @ X21 @ X21 @ X22 @ X24 @ X20))
% 0.46/0.63          | (v2_funct_1 @ X24)
% 0.46/0.63          | ((X22) = (k1_xboole_0))
% 0.46/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.46/0.63          | ~ (v1_funct_2 @ X24 @ X23 @ X21)
% 0.46/0.63          | ~ (v1_funct_1 @ X24))),
% 0.46/0.63      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.46/0.63          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.46/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.46/0.63        | (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((sk_A) = (k1_xboole_0))
% 0.46/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.63  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.63  thf('30', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('34', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.46/0.63  thf('35', plain, (~ (v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('clc', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.63  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.63  thf('38', plain, ((v1_xboole_0 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '36', '37'])).
% 0.46/0.63  thf(cc1_funct_1, axiom,
% 0.46/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.46/0.63  thf('39', plain, (![X1 : $i]: ((v1_funct_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.46/0.63  thf(cc2_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X2 : $i]:
% 0.46/0.63         ((v2_funct_1 @ X2)
% 0.46/0.63          | ~ (v1_funct_1 @ X2)
% 0.46/0.63          | ~ (v1_relat_1 @ X2)
% 0.46/0.63          | ~ (v1_xboole_0 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_xboole_0 @ X0)
% 0.46/0.63          | ~ (v1_xboole_0 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | (v2_funct_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.63  thf(cc1_relat_1, axiom,
% 0.46/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.46/0.63  thf('43', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.63  thf('44', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['42', '43'])).
% 0.46/0.63  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('sup-', [status(thm)], ['38', '44'])).
% 0.46/0.63  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
