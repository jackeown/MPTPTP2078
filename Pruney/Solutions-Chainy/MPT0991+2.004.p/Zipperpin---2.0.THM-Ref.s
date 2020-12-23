%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.udSq3hTTnI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:30 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 108 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  675 (1828 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
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
    ! [X6: $i] :
      ( ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
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
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
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
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X17 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
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
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['12','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.udSq3hTTnI
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 160 iterations in 0.144s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.40/0.60  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.60  thf(fc4_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.40/0.60  thf(t37_funct_2, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60            ( ?[D:$i]:
% 0.40/0.60              ( ( r2_relset_1 @
% 0.40/0.60                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.40/0.60                  ( k6_partfun1 @ A ) ) & 
% 0.40/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.40/0.60                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.40/0.60            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60               ( ?[D:$i]:
% 0.40/0.60                 ( ( r2_relset_1 @
% 0.40/0.60                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.40/0.60                     ( k6_partfun1 @ A ) ) & 
% 0.40/0.60                   ( m1_subset_1 @
% 0.40/0.60                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.40/0.60                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.40/0.60               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(cc1_subset_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_xboole_0 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X2 : $i, X3 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.40/0.60          | (v1_xboole_0 @ X2)
% 0.40/0.60          | ~ (v1_xboole_0 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(cc2_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.60       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X6 : $i]:
% 0.40/0.60         ((v2_funct_1 @ X6)
% 0.40/0.60          | ~ (v1_funct_1 @ X6)
% 0.40/0.60          | ~ (v1_relat_1 @ X6)
% 0.40/0.60          | ~ (v1_xboole_0 @ X6))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf(cc1_relat_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.40/0.60  thf('7', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf('8', plain, (((v2_funct_1 @ sk_C) | ~ (v1_xboole_0 @ sk_C))),
% 0.40/0.60      inference('clc', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain, (~ (v2_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('10', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.60      inference('clc', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf('11', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.40/0.60      inference('clc', [status(thm)], ['3', '10'])).
% 0.40/0.60  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.60        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.60        (k6_partfun1 @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.40/0.60  thf('14', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.60        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.60        (k6_relat_1 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(dt_k1_partfun1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.60         ( v1_funct_1 @ F ) & 
% 0.40/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.60       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.40/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.60          | ~ (v1_funct_1 @ X12)
% 0.40/0.60          | ~ (v1_funct_1 @ X15)
% 0.40/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.40/0.60          | (m1_subset_1 @ (k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15) @ 
% 0.40/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X17))))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.60          | ~ (v1_funct_1 @ X1)
% 0.40/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.40/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.60          | ~ (v1_funct_1 @ X1))),
% 0.40/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_D)
% 0.40/0.60        | (m1_subset_1 @ 
% 0.40/0.60           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '21'])).
% 0.40/0.60  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.60  thf(redefinition_r2_relset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.40/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.40/0.60          | ((X8) = (X11))
% 0.40/0.60          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.60             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.40/0.60          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.40/0.60        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.60            = (k6_relat_1 @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['15', '26'])).
% 0.40/0.60  thf(dt_k6_partfun1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( m1_subset_1 @
% 0.40/0.60         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.40/0.60       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X19 : $i]:
% 0.40/0.60         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.40/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.40/0.60  thf('29', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X19 : $i]:
% 0.40/0.60         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.40/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.40/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.60         = (k6_relat_1 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['27', '30'])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t26_funct_2, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ![E:$i]:
% 0.40/0.60         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.40/0.60             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.40/0.60           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.40/0.60             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.40/0.60               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.60         (~ (v1_funct_1 @ X21)
% 0.40/0.60          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.40/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X24 @ X22 @ X22 @ X23 @ X25 @ X21))
% 0.40/0.60          | (v2_funct_1 @ X25)
% 0.40/0.60          | ((X23) = (k1_xboole_0))
% 0.40/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.40/0.60          | ~ (v1_funct_2 @ X25 @ X24 @ X22)
% 0.40/0.60          | ~ (v1_funct_1 @ X25))),
% 0.40/0.60      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.40/0.60          | ((sk_A) = (k1_xboole_0))
% 0.40/0.60          | (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.40/0.60          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.40/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.40/0.60          | ((sk_A) = (k1_xboole_0))
% 0.40/0.60          | (v2_funct_1 @ X0)
% 0.40/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.40/0.60      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.40/0.60        | (v2_funct_1 @ sk_C)
% 0.40/0.60        | ((sk_A) = (k1_xboole_0))
% 0.40/0.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '37'])).
% 0.40/0.60  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.40/0.60  thf('39', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('43', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.40/0.60  thf('44', plain, (~ (v2_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.60      inference('clc', [status(thm)], ['43', '44'])).
% 0.40/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.60  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('47', plain, ($false),
% 0.40/0.60      inference('demod', [status(thm)], ['12', '45', '46'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
