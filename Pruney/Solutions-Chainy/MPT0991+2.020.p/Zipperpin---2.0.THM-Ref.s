%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqUpenl3fi

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:32 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 113 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  710 (1781 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X29 @ X27 @ X27 @ X28 @ X30 @ X26 ) )
      | ( v2_funct_1 @ X30 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('36',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','43','45'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['7','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aqUpenl3fi
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:50:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 426 iterations in 0.280s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.51/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.51/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.72  thf(cc1_funct_1, axiom,
% 0.51/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.51/0.72  thf('0', plain, (![X10 : $i]: ((v1_funct_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.51/0.72      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.51/0.72  thf(cc2_funct_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.72       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (![X11 : $i]:
% 0.51/0.72         ((v2_funct_1 @ X11)
% 0.51/0.72          | ~ (v1_funct_1 @ X11)
% 0.51/0.72          | ~ (v1_relat_1 @ X11)
% 0.51/0.72          | ~ (v1_xboole_0 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.51/0.72  thf('2', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (v1_xboole_0 @ X0)
% 0.51/0.72          | ~ (v1_xboole_0 @ X0)
% 0.51/0.72          | ~ (v1_relat_1 @ X0)
% 0.51/0.72          | (v2_funct_1 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['2'])).
% 0.51/0.72  thf(cc1_relat_1, axiom,
% 0.51/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.51/0.72  thf('4', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.51/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.51/0.72  thf('5', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.51/0.72      inference('clc', [status(thm)], ['3', '4'])).
% 0.51/0.72  thf(t37_funct_2, conjecture,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.72       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.51/0.72            ( ?[D:$i]:
% 0.51/0.72              ( ( r2_relset_1 @
% 0.51/0.72                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.51/0.72                  ( k6_partfun1 @ A ) ) & 
% 0.51/0.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.51/0.72                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.51/0.72            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.72          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.51/0.72               ( ?[D:$i]:
% 0.51/0.72                 ( ( r2_relset_1 @
% 0.51/0.72                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.51/0.72                     ( k6_partfun1 @ A ) ) & 
% 0.51/0.72                   ( m1_subset_1 @
% 0.51/0.72                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.51/0.72                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.51/0.72               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.51/0.72  thf('6', plain, (~ (v2_funct_1 @ sk_C)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('7', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.51/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf('8', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t3_subset, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (![X6 : $i, X7 : $i]:
% 0.51/0.72         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('10', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.51/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.72  thf('11', plain,
% 0.51/0.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.51/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.51/0.72        (k6_partfun1 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(dt_k1_partfun1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.72     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.51/0.72         ( v1_funct_1 @ F ) & 
% 0.51/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.51/0.72       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.51/0.72         ( m1_subset_1 @
% 0.51/0.72           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.51/0.72          | ~ (v1_funct_1 @ X19)
% 0.51/0.72          | ~ (v1_funct_1 @ X22)
% 0.51/0.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.51/0.72          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 0.51/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.51/0.72  thf('15', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.51/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.51/0.72          | ~ (v1_funct_1 @ X1)
% 0.51/0.72          | ~ (v1_funct_1 @ sk_C))),
% 0.51/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.72  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.51/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.51/0.72          | ~ (v1_funct_1 @ X1))),
% 0.51/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      ((~ (v1_funct_1 @ sk_D)
% 0.51/0.72        | (m1_subset_1 @ 
% 0.51/0.72           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.51/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['12', '17'])).
% 0.51/0.72  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      ((m1_subset_1 @ 
% 0.51/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.51/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.72  thf(redefinition_r2_relset_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.51/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.51/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.51/0.72          | ((X14) = (X17))
% 0.51/0.72          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.51/0.72  thf('22', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.51/0.72             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.51/0.72          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.72  thf('23', plain,
% 0.51/0.72      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.51/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.51/0.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.51/0.72            = (k6_partfun1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '22'])).
% 0.51/0.72  thf(t29_relset_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( m1_subset_1 @
% 0.51/0.72       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      (![X18 : $i]:
% 0.51/0.72         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 0.51/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.51/0.72  thf(redefinition_k6_partfun1, axiom,
% 0.51/0.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.51/0.72  thf('25', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      (![X18 : $i]:
% 0.51/0.72         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.51/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.51/0.72      inference('demod', [status(thm)], ['24', '25'])).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.51/0.72         = (k6_partfun1 @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['23', '26'])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t26_funct_2, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.72       ( ![E:$i]:
% 0.51/0.72         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.51/0.72             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.72           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.51/0.72             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.51/0.72               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.51/0.72  thf('29', plain,
% 0.51/0.72      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.51/0.72         (~ (v1_funct_1 @ X26)
% 0.51/0.72          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.51/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.51/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X29 @ X27 @ X27 @ X28 @ X30 @ X26))
% 0.51/0.72          | (v2_funct_1 @ X30)
% 0.51/0.72          | ((X28) = (k1_xboole_0))
% 0.51/0.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.51/0.72          | ~ (v1_funct_2 @ X30 @ X29 @ X27)
% 0.51/0.72          | ~ (v1_funct_1 @ X30))),
% 0.51/0.72      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.51/0.72  thf('30', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v1_funct_1 @ X0)
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.51/0.72          | ((sk_A) = (k1_xboole_0))
% 0.51/0.72          | (v2_funct_1 @ X0)
% 0.51/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.51/0.72          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.51/0.72          | ~ (v1_funct_1 @ sk_D))),
% 0.51/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('33', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v1_funct_1 @ X0)
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.51/0.72          | ((sk_A) = (k1_xboole_0))
% 0.51/0.72          | (v2_funct_1 @ X0)
% 0.51/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.51/0.72      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.51/0.72        | (v2_funct_1 @ sk_C)
% 0.51/0.72        | ((sk_A) = (k1_xboole_0))
% 0.51/0.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.51/0.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.51/0.72        | ~ (v1_funct_1 @ sk_C))),
% 0.51/0.72      inference('sup-', [status(thm)], ['27', '33'])).
% 0.51/0.72  thf(fc4_funct_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.51/0.72       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.51/0.72  thf('35', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.51/0.72  thf('36', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.51/0.72  thf('37', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 0.51/0.72      inference('demod', [status(thm)], ['35', '36'])).
% 0.51/0.72  thf('38', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('41', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.51/0.72      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 0.51/0.72  thf('42', plain, (~ (v2_funct_1 @ sk_C)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.51/0.72      inference('clc', [status(thm)], ['41', '42'])).
% 0.51/0.72  thf(t113_zfmisc_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      (![X4 : $i, X5 : $i]:
% 0.51/0.72         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.51/0.72  thf('45', plain,
% 0.51/0.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.72  thf('46', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.51/0.72      inference('demod', [status(thm)], ['10', '43', '45'])).
% 0.51/0.72  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.51/0.72  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.51/0.72      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.51/0.72  thf(t69_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.51/0.72       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.51/0.72  thf('48', plain,
% 0.51/0.72      (![X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r1_xboole_0 @ X1 @ X2)
% 0.51/0.72          | ~ (r1_tarski @ X1 @ X2)
% 0.51/0.72          | (v1_xboole_0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.51/0.72  thf('49', plain,
% 0.51/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.72  thf('50', plain, ((v1_xboole_0 @ sk_C)),
% 0.51/0.72      inference('sup-', [status(thm)], ['46', '49'])).
% 0.51/0.72  thf('51', plain, ($false), inference('demod', [status(thm)], ['7', '50'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
