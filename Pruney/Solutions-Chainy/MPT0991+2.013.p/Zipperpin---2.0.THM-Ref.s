%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeP9tc5Kwk

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:31 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 115 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  703 (1856 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('7',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['2','9'])).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X23 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
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
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X28 @ X26 @ X26 @ X27 @ X29 @ X25 ) )
      | ( v2_funct_1 @ X29 )
      | ( X27 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('36',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['10','43','45','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeP9tc5Kwk
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 240 iterations in 0.125s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.59  thf(t37_funct_2, conjecture,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.59       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.59            ( ?[D:$i]:
% 0.35/0.59              ( ( r2_relset_1 @
% 0.35/0.59                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.59                  ( k6_partfun1 @ A ) ) & 
% 0.35/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.35/0.59                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.35/0.59            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.59          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.59               ( ?[D:$i]:
% 0.35/0.59                 ( ( r2_relset_1 @
% 0.35/0.59                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.59                     ( k6_partfun1 @ A ) ) & 
% 0.35/0.59                   ( m1_subset_1 @
% 0.35/0.59                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.35/0.59                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.35/0.59               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(cc1_subset_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      (![X7 : $i, X8 : $i]:
% 0.35/0.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.35/0.59          | (v1_xboole_0 @ X7)
% 0.35/0.59          | ~ (v1_xboole_0 @ X8))),
% 0.35/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.35/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.59  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(cc2_funct_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.59       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.35/0.59  thf('4', plain,
% 0.35/0.59      (![X11 : $i]:
% 0.35/0.59         ((v2_funct_1 @ X11)
% 0.35/0.59          | ~ (v1_funct_1 @ X11)
% 0.35/0.59          | ~ (v1_relat_1 @ X11)
% 0.35/0.59          | ~ (v1_xboole_0 @ X11))),
% 0.35/0.59      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.35/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.59  thf(cc1_relat_1, axiom,
% 0.35/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.35/0.59  thf('6', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.35/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.35/0.59  thf('7', plain, (((v2_funct_1 @ sk_C) | ~ (v1_xboole_0 @ sk_C))),
% 0.35/0.59      inference('clc', [status(thm)], ['5', '6'])).
% 0.35/0.59  thf('8', plain, (~ (v2_funct_1 @ sk_C)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('9', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.35/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.35/0.59  thf('10', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.35/0.59      inference('clc', [status(thm)], ['2', '9'])).
% 0.35/0.59  thf('11', plain,
% 0.35/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.59        (k6_partfun1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(dt_k1_partfun1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.59         ( v1_funct_1 @ F ) & 
% 0.35/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.35/0.59         ( m1_subset_1 @
% 0.35/0.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.35/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.35/0.59  thf('14', plain,
% 0.35/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.35/0.59          | ~ (v1_funct_1 @ X18)
% 0.35/0.59          | ~ (v1_funct_1 @ X21)
% 0.35/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.35/0.59          | (m1_subset_1 @ (k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21) @ 
% 0.35/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X23))))),
% 0.35/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.59          | ~ (v1_funct_1 @ X1)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.59  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('17', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.59          | ~ (v1_funct_1 @ X1))),
% 0.35/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.59  thf('18', plain,
% 0.35/0.59      ((~ (v1_funct_1 @ sk_D)
% 0.35/0.59        | (m1_subset_1 @ 
% 0.35/0.59           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['12', '17'])).
% 0.35/0.59  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      ((m1_subset_1 @ 
% 0.35/0.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.35/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.35/0.59          | ((X13) = (X16))
% 0.35/0.59          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.59             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.35/0.59          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.35/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.59  thf('23', plain,
% 0.35/0.59      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.35/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.59        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.59            = (k6_partfun1 @ sk_A)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['11', '22'])).
% 0.35/0.59  thf(t29_relset_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( m1_subset_1 @
% 0.35/0.59       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (![X17 : $i]:
% 0.35/0.59         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.35/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.35/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.59  thf('25', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X17 : $i]:
% 0.35/0.59         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.35/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.35/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.59  thf('27', plain,
% 0.35/0.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.59         = (k6_partfun1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['23', '26'])).
% 0.35/0.59  thf('28', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(t26_funct_2, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.59       ( ![E:$i]:
% 0.35/0.59         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.35/0.59             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.35/0.59           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.35/0.59             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.59               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.59         (~ (v1_funct_1 @ X25)
% 0.35/0.59          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.35/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.35/0.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X28 @ X26 @ X26 @ X27 @ X29 @ X25))
% 0.35/0.59          | (v2_funct_1 @ X29)
% 0.35/0.59          | ((X27) = (k1_xboole_0))
% 0.35/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.35/0.59          | ~ (v1_funct_2 @ X29 @ X28 @ X26)
% 0.35/0.59          | ~ (v1_funct_1 @ X29))),
% 0.35/0.59      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.35/0.59  thf('30', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.35/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.35/0.59          | ((sk_A) = (k1_xboole_0))
% 0.35/0.59          | (v2_funct_1 @ X0)
% 0.35/0.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.35/0.59          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.35/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.59  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('33', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (v1_funct_1 @ X0)
% 0.35/0.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.35/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.35/0.59          | ((sk_A) = (k1_xboole_0))
% 0.35/0.59          | (v2_funct_1 @ X0)
% 0.35/0.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.35/0.59      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.35/0.59  thf('34', plain,
% 0.35/0.59      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.35/0.59        | (v2_funct_1 @ sk_C)
% 0.35/0.59        | ((sk_A) = (k1_xboole_0))
% 0.35/0.59        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.35/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.59        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.59      inference('sup-', [status(thm)], ['27', '33'])).
% 0.35/0.59  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.35/0.59  thf('35', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.35/0.59      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.35/0.59  thf('36', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.59  thf('37', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 0.35/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.35/0.59  thf('38', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('41', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.59      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 0.35/0.59  thf('42', plain, (~ (v2_funct_1 @ sk_C)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.35/0.59  thf(t113_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.59  thf('44', plain,
% 0.35/0.59      (![X5 : $i, X6 : $i]:
% 0.35/0.59         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.59  thf('45', plain,
% 0.35/0.59      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.35/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.35/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.59  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.59  thf('47', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.35/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.59  thf(t69_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.35/0.59       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.35/0.59  thf('48', plain,
% 0.35/0.59      (![X2 : $i, X3 : $i]:
% 0.35/0.59         (~ (r1_xboole_0 @ X2 @ X3)
% 0.35/0.59          | ~ (r1_tarski @ X2 @ X3)
% 0.35/0.59          | (v1_xboole_0 @ X2))),
% 0.35/0.59      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.35/0.59  thf('49', plain,
% 0.35/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.59  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.59      inference('sup-', [status(thm)], ['46', '49'])).
% 0.35/0.59  thf('51', plain, ($false),
% 0.35/0.59      inference('demod', [status(thm)], ['10', '43', '45', '50'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
