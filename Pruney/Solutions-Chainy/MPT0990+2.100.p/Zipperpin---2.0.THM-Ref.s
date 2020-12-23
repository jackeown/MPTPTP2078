%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QXwyoq1A1A

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:11 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  276 (15121 expanded)
%              Number of leaves         :   43 (4354 expanded)
%              Depth                    :   30
%              Number of atoms          : 2701 (413105 expanded)
%              Number of equality atoms :  219 (28652 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','34','35','36','39'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('42',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('46',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('65',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','65'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('71',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( zip_tseitin_0 @ X37 @ X40 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X41 @ X38 @ X38 @ X39 @ X40 @ X37 ) )
      | ( zip_tseitin_1 @ X39 @ X38 )
      | ( ( k2_relset_1 @ X41 @ X38 @ X40 )
       != X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('78',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ X43 @ ( k2_funct_1 @ X43 ) )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('82',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('96',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('97',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('107',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['95','109'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('126',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('128',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','128'])).

thf('130',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['76','129','130','131','132','133'])).

thf('135',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('137',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_funct_1 @ X34 )
      | ~ ( zip_tseitin_0 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('141',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','141'])).

thf('143',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('144',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ X43 @ ( k2_funct_1 @ X43 ) )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('146',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('154',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_partfun1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('161',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','164'])).

thf('166',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('168',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['143','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('173',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('175',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('177',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['142','177'])).

thf('179',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('181',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('183',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('185',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('188',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['188','189'])).

thf('191',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('192',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['180','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('195',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('197',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('199',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('201',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','201'])).

thf('203',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('205',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['203','207'])).

thf('209',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('210',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('212',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('214',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('216',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('219',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('221',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('222',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('224',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('226',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['202'])).

thf('228',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212','213','214','215','216','217','218','219','220','221','226','227'])).

thf('229',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['229','230'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QXwyoq1A1A
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:08:23 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.63/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.63/0.80  % Solved by: fo/fo7.sh
% 0.63/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.80  % done 564 iterations in 0.339s
% 0.63/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.63/0.80  % SZS output start Refutation
% 0.63/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.63/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.63/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.63/0.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.63/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.63/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.63/0.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.63/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.63/0.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.63/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.63/0.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.63/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.63/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.63/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.63/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.63/0.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.63/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.63/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.63/0.80  thf(t36_funct_2, conjecture,
% 0.63/0.80    (![A:$i,B:$i,C:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80       ( ![D:$i]:
% 0.63/0.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.63/0.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.63/0.80           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.63/0.80               ( r2_relset_1 @
% 0.63/0.80                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.63/0.80                 ( k6_partfun1 @ A ) ) & 
% 0.63/0.80               ( v2_funct_1 @ C ) ) =>
% 0.63/0.80             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.63/0.80               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.63/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.63/0.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80          ( ![D:$i]:
% 0.63/0.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.63/0.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.63/0.80              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.63/0.80                  ( r2_relset_1 @
% 0.63/0.80                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.63/0.80                    ( k6_partfun1 @ A ) ) & 
% 0.63/0.80                  ( v2_funct_1 @ C ) ) =>
% 0.63/0.80                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.63/0.80                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.63/0.80    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.63/0.80  thf('0', plain,
% 0.63/0.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.63/0.80        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.63/0.80        (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('1', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('2', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(redefinition_k1_partfun1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ E ) & 
% 0.63/0.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.80         ( v1_funct_1 @ F ) & 
% 0.63/0.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.63/0.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.63/0.80  thf('3', plain,
% 0.63/0.80      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.63/0.80          | ~ (v1_funct_1 @ X22)
% 0.63/0.80          | ~ (v1_funct_1 @ X25)
% 0.63/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.63/0.80          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.63/0.80              = (k5_relat_1 @ X22 @ X25)))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.63/0.80  thf('4', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.63/0.80            = (k5_relat_1 @ sk_C @ X0))
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.63/0.80  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('6', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.63/0.80            = (k5_relat_1 @ sk_C @ X0))
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['4', '5'])).
% 0.63/0.80  thf('7', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['1', '6'])).
% 0.63/0.80  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('9', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.80  thf('10', plain,
% 0.63/0.80      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.63/0.80        (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['0', '9'])).
% 0.63/0.80  thf('11', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('12', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(dt_k1_partfun1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ E ) & 
% 0.63/0.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.80         ( v1_funct_1 @ F ) & 
% 0.63/0.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.63/0.80       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.63/0.80         ( m1_subset_1 @
% 0.63/0.80           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.63/0.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.63/0.80  thf('13', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.63/0.80          | ~ (v1_funct_1 @ X16)
% 0.63/0.80          | ~ (v1_funct_1 @ X19)
% 0.63/0.80          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.63/0.80          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.63/0.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.63/0.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.63/0.80  thf('14', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.63/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.63/0.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ X1)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.63/0.80  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('16', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.63/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.63/0.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ X1))),
% 0.63/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.80  thf('17', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | (m1_subset_1 @ 
% 0.63/0.80           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.63/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['11', '16'])).
% 0.63/0.80  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('19', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.80  thf('20', plain,
% 0.63/0.80      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.63/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.63/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.63/0.80  thf(redefinition_r2_relset_1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.63/0.80  thf('21', plain,
% 0.63/0.80      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.63/0.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.63/0.80          | ((X11) = (X14))
% 0.63/0.80          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.63/0.80  thf('22', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.63/0.80          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.63/0.80  thf('23', plain,
% 0.63/0.80      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.63/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.63/0.80        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['10', '22'])).
% 0.63/0.80  thf(t29_relset_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( m1_subset_1 @
% 0.63/0.80       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.63/0.80  thf('24', plain,
% 0.63/0.80      (![X15 : $i]:
% 0.63/0.80         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 0.63/0.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.63/0.80  thf(redefinition_k6_partfun1, axiom,
% 0.63/0.80    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.63/0.80  thf('25', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('26', plain,
% 0.63/0.80      (![X15 : $i]:
% 0.63/0.80         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.63/0.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.63/0.80      inference('demod', [status(thm)], ['24', '25'])).
% 0.63/0.80  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.63/0.80  thf(t64_funct_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.63/0.80       ( ![B:$i]:
% 0.63/0.80         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.80           ( ( ( v2_funct_1 @ A ) & 
% 0.63/0.80               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.63/0.80               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.63/0.80             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.63/0.80  thf('28', plain,
% 0.63/0.80      (![X6 : $i, X7 : $i]:
% 0.63/0.80         (~ (v1_relat_1 @ X6)
% 0.63/0.80          | ~ (v1_funct_1 @ X6)
% 0.63/0.80          | ((X6) = (k2_funct_1 @ X7))
% 0.63/0.80          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.63/0.80          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.63/0.80          | ~ (v2_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_relat_1 @ X7))),
% 0.63/0.80      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.63/0.80  thf('29', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('30', plain,
% 0.63/0.80      (![X6 : $i, X7 : $i]:
% 0.63/0.80         (~ (v1_relat_1 @ X6)
% 0.63/0.80          | ~ (v1_funct_1 @ X6)
% 0.63/0.80          | ((X6) = (k2_funct_1 @ X7))
% 0.63/0.80          | ((k5_relat_1 @ X6 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 0.63/0.80          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.63/0.80          | ~ (v2_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_relat_1 @ X7))),
% 0.63/0.80      inference('demod', [status(thm)], ['28', '29'])).
% 0.63/0.80  thf('31', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_D)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.63/0.80        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | ~ (v1_relat_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['27', '30'])).
% 0.63/0.80  thf('32', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(cc1_relset_1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i]:
% 0.63/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.63/0.80       ( v1_relat_1 @ C ) ))).
% 0.63/0.80  thf('33', plain,
% 0.63/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.63/0.80         ((v1_relat_1 @ X8)
% 0.63/0.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.63/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.63/0.80  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.80  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('37', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('38', plain,
% 0.63/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.63/0.80         ((v1_relat_1 @ X8)
% 0.63/0.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.63/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.63/0.80  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('40', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.63/0.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.63/0.80      inference('demod', [status(thm)], ['31', '34', '35', '36', '39'])).
% 0.63/0.80  thf(t61_funct_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.63/0.80       ( ( v2_funct_1 @ A ) =>
% 0.63/0.80         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.63/0.80             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.63/0.80           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.63/0.80             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.63/0.80  thf('41', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.63/0.80              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.63/0.80  thf('42', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('43', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.63/0.80              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.63/0.80  thf('44', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(t35_funct_2, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.63/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.63/0.80           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.63/0.80             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.63/0.80  thf('45', plain,
% 0.63/0.80      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.63/0.80         (((X42) = (k1_xboole_0))
% 0.63/0.80          | ~ (v1_funct_1 @ X43)
% 0.63/0.80          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.63/0.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.63/0.80          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_partfun1 @ X42))
% 0.63/0.80          | ~ (v2_funct_1 @ X43)
% 0.63/0.80          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.63/0.80  thf('46', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_C)
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | ((sk_B) = (k1_xboole_0)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['44', '45'])).
% 0.63/0.80  thf('47', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('51', plain,
% 0.63/0.80      ((((sk_B) != (sk_B))
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ((sk_B) = (k1_xboole_0)))),
% 0.63/0.80      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.63/0.80  thf('52', plain,
% 0.63/0.80      ((((sk_B) = (k1_xboole_0))
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['51'])).
% 0.63/0.80  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('54', plain,
% 0.63/0.80      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.63/0.80  thf('55', plain,
% 0.63/0.80      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_C)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup+', [status(thm)], ['43', '54'])).
% 0.63/0.80  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('59', plain,
% 0.63/0.80      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 0.63/0.80      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.63/0.80  thf(t71_relat_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.63/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.63/0.80  thf('60', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.63/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.63/0.80  thf('61', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('62', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('63', plain,
% 0.63/0.80      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.63/0.80      inference('sup+', [status(thm)], ['59', '62'])).
% 0.63/0.80  thf('64', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('65', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.63/0.80      inference('demod', [status(thm)], ['63', '64'])).
% 0.63/0.80  thf('66', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.63/0.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.63/0.80      inference('demod', [status(thm)], ['40', '65'])).
% 0.63/0.80  thf('67', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.80  thf('68', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.63/0.80  thf('69', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['67', '68'])).
% 0.63/0.80  thf('70', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(t30_funct_2, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.80     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.80         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.63/0.80       ( ![E:$i]:
% 0.63/0.80         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.63/0.80             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.63/0.80           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.63/0.80               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.63/0.80             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.63/0.80               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.63/0.80  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.63/0.80  thf(zf_stmt_2, axiom,
% 0.63/0.80    (![C:$i,B:$i]:
% 0.63/0.80     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.63/0.80       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.63/0.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.63/0.80  thf(zf_stmt_4, axiom,
% 0.63/0.80    (![E:$i,D:$i]:
% 0.63/0.80     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.63/0.80  thf(zf_stmt_5, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.63/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80       ( ![E:$i]:
% 0.63/0.80         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.63/0.80             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.63/0.80           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.63/0.80               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.63/0.80             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.63/0.80  thf('71', plain,
% 0.63/0.80      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X37)
% 0.63/0.80          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.63/0.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.63/0.80          | (zip_tseitin_0 @ X37 @ X40)
% 0.63/0.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X41 @ X38 @ X38 @ X39 @ X40 @ X37))
% 0.63/0.80          | (zip_tseitin_1 @ X39 @ X38)
% 0.63/0.80          | ((k2_relset_1 @ X41 @ X38 @ X40) != (X38))
% 0.63/0.80          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X38)))
% 0.63/0.80          | ~ (v1_funct_2 @ X40 @ X41 @ X38)
% 0.63/0.80          | ~ (v1_funct_1 @ X40))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.63/0.80  thf('72', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.63/0.80          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.63/0.80          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.63/0.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.63/0.80          | (zip_tseitin_0 @ sk_D @ X0)
% 0.63/0.80          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_D))),
% 0.63/0.80      inference('sup-', [status(thm)], ['70', '71'])).
% 0.63/0.80  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('75', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.63/0.80          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.63/0.80          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.63/0.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.63/0.80          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.63/0.80  thf('76', plain,
% 0.63/0.80      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.63/0.80        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.63/0.80        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.63/0.80        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.63/0.80        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['69', '75'])).
% 0.63/0.80  thf('77', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.63/0.80              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.63/0.80  thf('78', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('79', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.63/0.80              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('demod', [status(thm)], ['77', '78'])).
% 0.63/0.80  thf('80', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('81', plain,
% 0.63/0.80      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.63/0.80         (((X42) = (k1_xboole_0))
% 0.63/0.80          | ~ (v1_funct_1 @ X43)
% 0.63/0.80          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.63/0.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.63/0.80          | ((k5_relat_1 @ X43 @ (k2_funct_1 @ X43)) = (k6_partfun1 @ X44))
% 0.63/0.80          | ~ (v2_funct_1 @ X43)
% 0.63/0.80          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.63/0.80  thf('82', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_C)
% 0.63/0.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | ((sk_B) = (k1_xboole_0)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['80', '81'])).
% 0.63/0.80  thf('83', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('85', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('87', plain,
% 0.63/0.80      ((((sk_B) != (sk_B))
% 0.63/0.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ((sk_B) = (k1_xboole_0)))),
% 0.63/0.80      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.63/0.80  thf('88', plain,
% 0.63/0.80      ((((sk_B) = (k1_xboole_0))
% 0.63/0.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['87'])).
% 0.63/0.80  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('90', plain,
% 0.63/0.80      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.63/0.80  thf('91', plain,
% 0.63/0.80      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_C)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup+', [status(thm)], ['79', '90'])).
% 0.63/0.80  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('95', plain,
% 0.63/0.80      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.63/0.80  thf(t78_relat_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( ( v1_relat_1 @ A ) =>
% 0.63/0.80       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.63/0.80  thf('96', plain,
% 0.63/0.80      (![X2 : $i]:
% 0.63/0.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X2)) @ X2) = (X2))
% 0.63/0.80          | ~ (v1_relat_1 @ X2))),
% 0.63/0.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.63/0.80  thf('97', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('98', plain,
% 0.63/0.80      (![X2 : $i]:
% 0.63/0.80         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X2)) @ X2) = (X2))
% 0.63/0.80          | ~ (v1_relat_1 @ X2))),
% 0.63/0.80      inference('demod', [status(thm)], ['96', '97'])).
% 0.63/0.80  thf(t48_funct_1, axiom,
% 0.63/0.80    (![A:$i]:
% 0.63/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.63/0.80       ( ![B:$i]:
% 0.63/0.80         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.80           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.63/0.80               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.63/0.80             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.63/0.80  thf('99', plain,
% 0.63/0.80      (![X3 : $i, X4 : $i]:
% 0.63/0.80         (~ (v1_relat_1 @ X3)
% 0.63/0.80          | ~ (v1_funct_1 @ X3)
% 0.63/0.80          | (v2_funct_1 @ X3)
% 0.63/0.80          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.63/0.80          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.63/0.80          | ~ (v1_funct_1 @ X4)
% 0.63/0.80          | ~ (v1_relat_1 @ X4))),
% 0.63/0.80      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.63/0.80  thf('100', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ((k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80              != (k1_relat_1 @ X0))
% 0.63/0.80          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['98', '99'])).
% 0.63/0.80  thf('101', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.63/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.63/0.80  thf('102', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.63/0.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.63/0.80  thf('103', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.63/0.80      inference('demod', [status(thm)], ['101', '102'])).
% 0.63/0.80  thf('104', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.63/0.80          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.63/0.80      inference('demod', [status(thm)], ['100', '103'])).
% 0.63/0.80  thf('105', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v2_funct_1 @ X0))),
% 0.63/0.80      inference('simplify', [status(thm)], ['104'])).
% 0.63/0.80  thf('106', plain,
% 0.63/0.80      (![X15 : $i]:
% 0.63/0.80         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.63/0.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.63/0.80      inference('demod', [status(thm)], ['24', '25'])).
% 0.63/0.80  thf('107', plain,
% 0.63/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.63/0.80         ((v1_relat_1 @ X8)
% 0.63/0.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.63/0.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.63/0.80  thf('108', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.63/0.80      inference('sup-', [status(thm)], ['106', '107'])).
% 0.63/0.80  thf('109', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v2_funct_1 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['105', '108'])).
% 0.63/0.80  thf('110', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_C)
% 0.63/0.80        | ~ (v1_relat_1 @ sk_C)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80        | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['95', '109'])).
% 0.63/0.80  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('114', plain,
% 0.63/0.80      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.63/0.80  thf('115', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.63/0.80        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.63/0.80      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.63/0.80  thf('116', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('117', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('118', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.63/0.80          | ~ (v1_funct_1 @ X16)
% 0.63/0.80          | ~ (v1_funct_1 @ X19)
% 0.63/0.80          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.63/0.80          | (v1_funct_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19)))),
% 0.63/0.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.63/0.80  thf('119', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['117', '118'])).
% 0.63/0.80  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('121', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.80         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['119', '120'])).
% 0.63/0.80  thf('122', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['116', '121'])).
% 0.63/0.80  thf('123', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('124', plain,
% 0.63/0.80      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['122', '123'])).
% 0.63/0.80  thf('125', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.80  thf('126', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['124', '125'])).
% 0.63/0.80  thf('127', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.63/0.80  thf('128', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['126', '127'])).
% 0.63/0.80  thf('129', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['115', '128'])).
% 0.63/0.80  thf('130', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('131', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('132', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('134', plain,
% 0.63/0.80      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.63/0.80        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.63/0.80        | ((sk_B) != (sk_B)))),
% 0.63/0.80      inference('demod', [status(thm)],
% 0.63/0.80                ['76', '129', '130', '131', '132', '133'])).
% 0.63/0.80  thf('135', plain,
% 0.63/0.80      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.63/0.80      inference('simplify', [status(thm)], ['134'])).
% 0.63/0.80  thf('136', plain,
% 0.63/0.80      (![X35 : $i, X36 : $i]:
% 0.63/0.80         (((X35) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X35 @ X36))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.63/0.80  thf('137', plain,
% 0.63/0.80      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['135', '136'])).
% 0.63/0.80  thf('138', plain, (((sk_A) != (k1_xboole_0))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('139', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.63/0.80  thf('140', plain,
% 0.63/0.80      (![X33 : $i, X34 : $i]:
% 0.63/0.80         ((v2_funct_1 @ X34) | ~ (zip_tseitin_0 @ X34 @ X33))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.63/0.80  thf('141', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('142', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.63/0.80        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.63/0.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.63/0.80      inference('demod', [status(thm)], ['66', '141'])).
% 0.63/0.80  thf('143', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.63/0.80              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('demod', [status(thm)], ['77', '78'])).
% 0.63/0.80  thf('144', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('145', plain,
% 0.63/0.80      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.63/0.80         (((X42) = (k1_xboole_0))
% 0.63/0.80          | ~ (v1_funct_1 @ X43)
% 0.63/0.80          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.63/0.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.63/0.80          | ((k5_relat_1 @ X43 @ (k2_funct_1 @ X43)) = (k6_partfun1 @ X44))
% 0.63/0.80          | ~ (v2_funct_1 @ X43)
% 0.63/0.80          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.63/0.80  thf('146', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['144', '145'])).
% 0.63/0.80  thf('147', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('149', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.63/0.80      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.63/0.80  thf('150', plain, (((sk_A) != (k1_xboole_0))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('151', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.63/0.80  thf('152', plain,
% 0.63/0.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.63/0.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.80  thf('153', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(t24_funct_2, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i]:
% 0.63/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.80       ( ![D:$i]:
% 0.63/0.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.63/0.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.63/0.80           ( ( r2_relset_1 @
% 0.63/0.80               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.63/0.80               ( k6_partfun1 @ B ) ) =>
% 0.63/0.80             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.63/0.80  thf('154', plain,
% 0.63/0.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X29)
% 0.63/0.80          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.63/0.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.63/0.80          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 0.63/0.80               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 0.63/0.80               (k6_partfun1 @ X30))
% 0.63/0.80          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 0.63/0.80          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.63/0.80          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.63/0.80          | ~ (v1_funct_1 @ X32))),
% 0.63/0.80      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.63/0.80  thf('155', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.63/0.80          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.63/0.80          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.63/0.80               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.63/0.80               (k6_partfun1 @ sk_A))
% 0.63/0.80          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('sup-', [status(thm)], ['153', '154'])).
% 0.63/0.80  thf('156', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('158', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.63/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.63/0.80          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.63/0.80          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.63/0.80               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.63/0.80               (k6_partfun1 @ sk_A)))),
% 0.63/0.80      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.63/0.80  thf('159', plain,
% 0.63/0.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.63/0.80           (k6_partfun1 @ sk_A))
% 0.63/0.80        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.63/0.80        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D))),
% 0.63/0.80      inference('sup-', [status(thm)], ['152', '158'])).
% 0.63/0.80  thf('160', plain,
% 0.63/0.80      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.63/0.80        (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['0', '9'])).
% 0.63/0.80  thf('161', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('162', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('163', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('164', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 0.63/0.80  thf('165', plain,
% 0.63/0.80      ((((sk_A) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.63/0.80      inference('demod', [status(thm)], ['151', '164'])).
% 0.63/0.80  thf('166', plain,
% 0.63/0.80      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['165'])).
% 0.63/0.80  thf('167', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('168', plain,
% 0.63/0.80      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.63/0.80      inference('demod', [status(thm)], ['166', '167'])).
% 0.63/0.80  thf('169', plain,
% 0.63/0.80      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_D)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D))),
% 0.63/0.80      inference('sup+', [status(thm)], ['143', '168'])).
% 0.63/0.80  thf('170', plain, ((v1_relat_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.80  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('172', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('173', plain,
% 0.63/0.80      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.63/0.80      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 0.63/0.80  thf('174', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('175', plain,
% 0.63/0.80      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.63/0.80      inference('sup+', [status(thm)], ['173', '174'])).
% 0.63/0.80  thf('176', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('177', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['175', '176'])).
% 0.63/0.80  thf('178', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.63/0.80        | ((sk_B) != (sk_B))
% 0.63/0.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.63/0.80      inference('demod', [status(thm)], ['142', '177'])).
% 0.63/0.80  thf('179', plain,
% 0.63/0.80      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.63/0.80        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 0.63/0.80      inference('simplify', [status(thm)], ['178'])).
% 0.63/0.80  thf('180', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.63/0.80              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.63/0.80  thf('181', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('182', plain,
% 0.63/0.80      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.63/0.80         (((X42) = (k1_xboole_0))
% 0.63/0.80          | ~ (v1_funct_1 @ X43)
% 0.63/0.80          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.63/0.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.63/0.80          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_partfun1 @ X42))
% 0.63/0.80          | ~ (v2_funct_1 @ X43)
% 0.63/0.80          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.63/0.80  thf('183', plain,
% 0.63/0.80      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['181', '182'])).
% 0.63/0.80  thf('184', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 0.63/0.80  thf('185', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('186', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('187', plain,
% 0.63/0.80      ((((sk_A) != (sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.63/0.80      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 0.63/0.80  thf('188', plain,
% 0.63/0.80      ((((sk_A) = (k1_xboole_0))
% 0.63/0.80        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['187'])).
% 0.63/0.80  thf('189', plain, (((sk_A) != (k1_xboole_0))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('190', plain,
% 0.63/0.80      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['188', '189'])).
% 0.63/0.80  thf('191', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('192', plain,
% 0.63/0.80      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['190', '191'])).
% 0.63/0.80  thf('193', plain,
% 0.63/0.80      ((((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_D)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D))),
% 0.63/0.80      inference('sup+', [status(thm)], ['180', '192'])).
% 0.63/0.80  thf('194', plain, ((v1_relat_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.80  thf('195', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('196', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('197', plain,
% 0.63/0.80      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.63/0.80  thf('198', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('199', plain,
% 0.63/0.80      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k2_relat_1 @ sk_D))),
% 0.63/0.80      inference('sup+', [status(thm)], ['197', '198'])).
% 0.63/0.80  thf('200', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('201', plain, (((sk_A) = (k2_relat_1 @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['199', '200'])).
% 0.63/0.80  thf('202', plain,
% 0.63/0.80      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.63/0.80        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 0.63/0.80      inference('demod', [status(thm)], ['179', '201'])).
% 0.63/0.80  thf('203', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('204', plain,
% 0.63/0.80      (![X5 : $i]:
% 0.63/0.80         (~ (v2_funct_1 @ X5)
% 0.63/0.80          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.63/0.80              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 0.63/0.80          | ~ (v1_funct_1 @ X5)
% 0.63/0.80          | ~ (v1_relat_1 @ X5))),
% 0.63/0.80      inference('demod', [status(thm)], ['77', '78'])).
% 0.63/0.80  thf('205', plain,
% 0.63/0.80      (![X6 : $i, X7 : $i]:
% 0.63/0.80         (~ (v1_relat_1 @ X6)
% 0.63/0.80          | ~ (v1_funct_1 @ X6)
% 0.63/0.80          | ((X6) = (k2_funct_1 @ X7))
% 0.63/0.80          | ((k5_relat_1 @ X6 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 0.63/0.80          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.63/0.80          | ~ (v2_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_funct_1 @ X7)
% 0.63/0.80          | ~ (v1_relat_1 @ X7))),
% 0.63/0.80      inference('demod', [status(thm)], ['28', '29'])).
% 0.63/0.80  thf('206', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.63/0.80            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v2_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.63/0.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0))),
% 0.63/0.80      inference('sup-', [status(thm)], ['204', '205'])).
% 0.63/0.80  thf('207', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.63/0.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.63/0.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.63/0.80          | ~ (v2_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_funct_1 @ X0)
% 0.63/0.80          | ~ (v1_relat_1 @ X0)
% 0.63/0.80          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.63/0.80              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.63/0.80      inference('simplify', [status(thm)], ['206'])).
% 0.63/0.80  thf('208', plain,
% 0.63/0.80      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.63/0.80          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.63/0.80        | ~ (v1_relat_1 @ sk_D)
% 0.63/0.80        | ~ (v1_funct_1 @ sk_D)
% 0.63/0.80        | ~ (v2_funct_1 @ sk_D)
% 0.63/0.80        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.63/0.80        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.63/0.80        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.63/0.80        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.63/0.80        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['203', '207'])).
% 0.63/0.80  thf('209', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['175', '176'])).
% 0.63/0.80  thf('210', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.63/0.80      inference('demod', [status(thm)], ['63', '64'])).
% 0.63/0.80  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.80  thf('212', plain, ((v1_funct_1 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('213', plain, ((v2_funct_1 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('214', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('216', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('218', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('219', plain, ((v2_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('220', plain, (((sk_A) = (k2_relat_1 @ sk_D))),
% 0.63/0.80      inference('demod', [status(thm)], ['199', '200'])).
% 0.63/0.80  thf('221', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('222', plain,
% 0.63/0.80      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.63/0.80      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.63/0.80  thf('223', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('224', plain,
% 0.63/0.80      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.63/0.80      inference('sup+', [status(thm)], ['222', '223'])).
% 0.63/0.80  thf('225', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.63/0.80  thf('226', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.63/0.80      inference('demod', [status(thm)], ['224', '225'])).
% 0.63/0.80  thf('227', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.63/0.80      inference('simplify', [status(thm)], ['202'])).
% 0.63/0.80  thf('228', plain,
% 0.63/0.80      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.63/0.80        | ((sk_A) != (sk_A))
% 0.63/0.80        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.63/0.80      inference('demod', [status(thm)],
% 0.63/0.80                ['208', '209', '210', '211', '212', '213', '214', '215', 
% 0.63/0.80                 '216', '217', '218', '219', '220', '221', '226', '227'])).
% 0.63/0.80  thf('229', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.63/0.80      inference('simplify', [status(thm)], ['228'])).
% 0.63/0.80  thf('230', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('231', plain, ($false),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['229', '230'])).
% 0.63/0.80  
% 0.63/0.80  % SZS output end Refutation
% 0.63/0.80  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
