%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7lyoa2FbI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:30 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 116 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  706 (1859 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['3','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
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

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['43','44'])).

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
    inference(demod,[status(thm)],['12','45','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7lyoa2FbI
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 268 iterations in 0.269s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.50/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.50/0.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.72  thf(fc4_zfmisc_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.50/0.72      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.50/0.72  thf(t37_funct_2, conjecture,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.72       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.50/0.72            ( ?[D:$i]:
% 0.50/0.72              ( ( r2_relset_1 @
% 0.50/0.72                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.50/0.72                  ( k6_partfun1 @ A ) ) & 
% 0.50/0.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.50/0.72                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.50/0.72            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.72          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.50/0.72               ( ?[D:$i]:
% 0.50/0.72                 ( ( r2_relset_1 @
% 0.50/0.72                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.50/0.72                     ( k6_partfun1 @ A ) ) & 
% 0.50/0.72                   ( m1_subset_1 @
% 0.50/0.72                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.50/0.72                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.50/0.72               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(cc1_subset_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( v1_xboole_0 @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.50/0.72          | (v1_xboole_0 @ X6)
% 0.50/0.72          | ~ (v1_xboole_0 @ X7))),
% 0.50/0.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.72  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(cc2_funct_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.72       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X10 : $i]:
% 0.50/0.72         ((v2_funct_1 @ X10)
% 0.50/0.72          | ~ (v1_funct_1 @ X10)
% 0.50/0.72          | ~ (v1_relat_1 @ X10)
% 0.50/0.72          | ~ (v1_xboole_0 @ X10))),
% 0.50/0.72      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.72  thf(cc1_relat_1, axiom,
% 0.50/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.50/0.72  thf('7', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.50/0.72  thf('8', plain, (((v2_funct_1 @ sk_C) | ~ (v1_xboole_0 @ sk_C))),
% 0.50/0.72      inference('clc', [status(thm)], ['6', '7'])).
% 0.50/0.72  thf('9', plain, (~ (v2_funct_1 @ sk_C)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('10', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.50/0.72      inference('clc', [status(thm)], ['8', '9'])).
% 0.50/0.72  thf('11', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.72      inference('clc', [status(thm)], ['3', '10'])).
% 0.50/0.72  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.50/0.72      inference('sup-', [status(thm)], ['0', '11'])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.50/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.72        (k6_partfun1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(redefinition_k6_partfun1, axiom,
% 0.50/0.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.50/0.72  thf('14', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.50/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.72        (k6_relat_1 @ sk_A))),
% 0.50/0.72      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(dt_k1_partfun1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.50/0.72     ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.72         ( v1_funct_1 @ F ) & 
% 0.50/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.50/0.72       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.50/0.72         ( m1_subset_1 @
% 0.50/0.72           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.50/0.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.50/0.72  thf('18', plain,
% 0.50/0.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.50/0.72          | ~ (v1_funct_1 @ X16)
% 0.50/0.72          | ~ (v1_funct_1 @ X19)
% 0.50/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.50/0.72          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.50/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.50/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.50/0.72          | ~ (v1_funct_1 @ X1)
% 0.50/0.72          | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.72  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.50/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.50/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.50/0.72          | ~ (v1_funct_1 @ X1))),
% 0.50/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      ((~ (v1_funct_1 @ sk_D)
% 0.50/0.72        | (m1_subset_1 @ 
% 0.50/0.72           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['16', '21'])).
% 0.50/0.72  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      ((m1_subset_1 @ 
% 0.50/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.50/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.50/0.72  thf(redefinition_r2_relset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.50/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.50/0.72          | ((X12) = (X15))
% 0.50/0.72          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.50/0.72             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.50/0.72          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.50/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.50/0.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.50/0.72            = (k6_relat_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['15', '26'])).
% 0.50/0.72  thf(dt_k6_partfun1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( m1_subset_1 @
% 0.50/0.72         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.50/0.72       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      (![X23 : $i]:
% 0.50/0.72         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.50/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.50/0.72  thf('29', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      (![X23 : $i]:
% 0.50/0.72         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.50/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.50/0.72      inference('demod', [status(thm)], ['28', '29'])).
% 0.50/0.72  thf('31', plain,
% 0.50/0.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.50/0.72         = (k6_relat_1 @ sk_A))),
% 0.50/0.72      inference('demod', [status(thm)], ['27', '30'])).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t26_funct_2, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.72       ( ![E:$i]:
% 0.50/0.72         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.50/0.72             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.50/0.72           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.50/0.72             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.72               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.50/0.72  thf('33', plain,
% 0.50/0.72      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.72         (~ (v1_funct_1 @ X25)
% 0.50/0.72          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.50/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.50/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X28 @ X26 @ X26 @ X27 @ X29 @ X25))
% 0.50/0.72          | (v2_funct_1 @ X29)
% 0.50/0.72          | ((X27) = (k1_xboole_0))
% 0.50/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.50/0.72          | ~ (v1_funct_2 @ X29 @ X28 @ X26)
% 0.50/0.72          | ~ (v1_funct_1 @ X29))),
% 0.50/0.72      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_funct_1 @ X0)
% 0.50/0.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.50/0.72          | ((sk_A) = (k1_xboole_0))
% 0.50/0.72          | (v2_funct_1 @ X0)
% 0.50/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.50/0.72          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.50/0.72          | ~ (v1_funct_1 @ sk_D))),
% 0.50/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.50/0.72  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_funct_1 @ X0)
% 0.50/0.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.50/0.72          | ((sk_A) = (k1_xboole_0))
% 0.50/0.72          | (v2_funct_1 @ X0)
% 0.50/0.72          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.50/0.72      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.50/0.72  thf('38', plain,
% 0.50/0.72      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.50/0.72        | (v2_funct_1 @ sk_C)
% 0.50/0.72        | ((sk_A) = (k1_xboole_0))
% 0.50/0.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.50/0.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.50/0.72        | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.72      inference('sup-', [status(thm)], ['31', '37'])).
% 0.50/0.72  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.50/0.72  thf('39', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 0.50/0.72      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('43', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.50/0.72      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.50/0.72  thf('44', plain, (~ (v2_funct_1 @ sk_C)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.50/0.72      inference('clc', [status(thm)], ['43', '44'])).
% 0.50/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.72  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.72  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.50/0.72  thf('47', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.50/0.72      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.50/0.72  thf(t69_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.50/0.72       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.50/0.72  thf('48', plain,
% 0.50/0.72      (![X2 : $i, X3 : $i]:
% 0.50/0.72         (~ (r1_xboole_0 @ X2 @ X3)
% 0.50/0.72          | ~ (r1_tarski @ X2 @ X3)
% 0.50/0.72          | (v1_xboole_0 @ X2))),
% 0.50/0.72      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.50/0.72  thf('49', plain,
% 0.50/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.72  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.72      inference('sup-', [status(thm)], ['46', '49'])).
% 0.50/0.72  thf('51', plain, ($false),
% 0.50/0.72      inference('demod', [status(thm)], ['12', '45', '50'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
