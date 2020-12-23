%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WP4ytrNKuI

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:20 EST 2020

% Result     : Theorem 4.97s
% Output     : Refutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  468 (6073 expanded)
%              Number of leaves         :   55 (1975 expanded)
%              Depth                    :   43
%              Number of atoms          : 4277 (108205 expanded)
%              Number of equality atoms :  288 (7958 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('4',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
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

thf('7',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( X64 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X66 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X64 ) ) )
      | ( ( k5_relat_1 @ X65 @ ( k2_funct_1 @ X65 ) )
        = ( k6_partfun1 @ X66 ) )
      | ~ ( v2_funct_1 @ X65 )
      | ( ( k2_relset_1 @ X66 @ X64 @ X65 )
       != X64 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('8',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('30',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X23: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X23 ) )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('36',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X23: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X23 ) )
      = ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('42',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','43','46','49'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','43','46','49'])).

thf('62',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('66',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','23','67'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('71',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('76',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( r2_relset_1 @ X58 @ X58 @ ( k1_partfun1 @ X58 @ X59 @ X59 @ X58 @ X57 @ X60 ) @ ( k6_partfun1 @ X58 ) )
      | ( ( k2_relset_1 @ X59 @ X58 @ X60 )
        = X58 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X59 @ X58 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('87',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['84','87','88','89','90'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('93',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('101',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['93','98'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('108',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['76','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( X64 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X66 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X64 ) ) )
      | ( ( k5_relat_1 @ X65 @ ( k2_funct_1 @ X65 ) )
        = ( k6_partfun1 @ X66 ) )
      | ~ ( v2_funct_1 @ X65 )
      | ( ( k2_relset_1 @ X66 @ X64 @ X65 )
       != X64 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('115',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('117',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['84','87','88','89','90'])).

thf('123',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
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

thf('128',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53 )
        = ( k5_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['125','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
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

thf('138',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('145',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('146',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','147'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('149',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

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

thf('151',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('152',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('154',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('155',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('157',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('158',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('159',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('160',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('161',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('162',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('163',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('168',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('169',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['159','166','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('173',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','170','171','172'])).

thf('174',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['124','174'])).

thf('176',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['159','166','169'])).

thf('177',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('178',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['176','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('185',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['173'])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( X64 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X66 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X64 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X65 ) @ X65 )
        = ( k6_partfun1 @ X64 ) )
      | ~ ( v2_funct_1 @ X65 )
      | ( ( k2_relset_1 @ X66 @ X64 @ X65 )
       != X64 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('192',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['192','193','194','195','196'])).

thf('198',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['189','205'])).

thf('207',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('209',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('213',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['210','213'])).

thf('215',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('219',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('222',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('228',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','226','227'])).

thf('229',plain,(
    ! [X23: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X23 ) )
      = ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('230',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('233',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('234',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['228','235'])).

thf('237',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','23','67'])).

thf('239',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('241',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','43','46','49'])).

thf('243',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('245',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('246',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('247',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('248',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('249',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('250',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('251',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('252',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('253',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('254',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['252','261'])).

thf('263',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('264',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('265',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('266',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('267',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('269',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('270',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('271',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('272',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('277',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('279',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('280',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('281',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['262','263','264','267','268','269','270','275','276','277','278','281'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['251','283'])).

thf('285',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['250','284'])).

thf('286',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('289',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['285','286','287','288'])).

thf('290',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['249','289'])).

thf('291',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('293',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('294',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('295',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['290','291','292','293','294','295','296'])).

thf('298',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['248','297'])).

thf('299',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf('300',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('301',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('302',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['298','299','300','301','302','303'])).

thf('305',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['247','304'])).

thf('306',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf('307',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('308',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('309',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['305','306','307','308','309','310'])).

thf('312',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('313',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('317',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['313','314','315','316'])).

thf('318',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['246','317'])).

thf('319',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('320',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['318','319','320'])).

thf('322',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['245','321'])).

thf('323',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('324',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['244','325'])).

thf('327',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('328',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('329',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['326','327','328','329','330'])).

thf('332',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','332'])).

thf('334',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('335',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','43','46','49'])).

thf('336',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['335','336'])).

thf('338',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['334','337'])).

thf('339',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('340',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('341',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('343',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['338','339','340','341','342','343','344'])).

thf('346',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('347',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('348',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['333','347'])).

thf('349',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['240','348'])).

thf('350',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('351',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('353',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('354',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('355',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('356',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['354','358'])).

thf('360',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('361',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('362',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('365',plain,
    ( ( k2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['359','360','361','362','363','364'])).

thf('366',plain,
    ( ( ( k2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['353','365'])).

thf('367',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('368',plain,(
    ! [X23: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X23 ) )
      = ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('369',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('370',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['366','367','368','369','370','371'])).

thf('373',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['279','280'])).

thf('374',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['372','373'])).

thf('375',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['279','280'])).

thf('376',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['374','375'])).

thf('377',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('378',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('379',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('380',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('381',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('382',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('383',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['381','382'])).

thf('384',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('385',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('386',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('387',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('388',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('389',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['383','384','385','386','387','388'])).

thf('390',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('392',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['390','391'])).

thf('393',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['239','352','376','377','378','379','380','392'])).

thf('394',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('395',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['173'])).

thf('397',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['236','393','394','395','396'])).

thf('398',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['188','397'])).

thf('399',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['175','398'])).

thf('400',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','399'])).

thf('401',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','400'])).

thf('402',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('403',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','216','219'])).

thf('404',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['93','98'])).

thf('405',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('406',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','66'])).

thf('409',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['401','402','403','404','405','406','407','408'])).

thf('410',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['409','410'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WP4ytrNKuI
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.97/5.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.97/5.17  % Solved by: fo/fo7.sh
% 4.97/5.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.97/5.17  % done 1737 iterations in 4.712s
% 4.97/5.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.97/5.17  % SZS output start Refutation
% 4.97/5.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.97/5.17  thf(sk_B_type, type, sk_B: $i).
% 4.97/5.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.97/5.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.97/5.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.97/5.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.97/5.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.97/5.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.97/5.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.97/5.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.97/5.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.97/5.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.97/5.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.97/5.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.97/5.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.97/5.17  thf(sk_A_type, type, sk_A: $i).
% 4.97/5.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.97/5.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.97/5.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.97/5.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.97/5.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.97/5.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.97/5.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.97/5.17  thf(sk_C_type, type, sk_C: $i).
% 4.97/5.17  thf(sk_D_type, type, sk_D: $i).
% 4.97/5.17  thf(t61_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.17       ( ( v2_funct_1 @ A ) =>
% 4.97/5.17         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 4.97/5.17             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 4.97/5.17           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 4.97/5.17             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.97/5.17  thf('0', plain,
% 4.97/5.17      (![X20 : $i]:
% 4.97/5.17         (~ (v2_funct_1 @ X20)
% 4.97/5.17          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.17              = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 4.97/5.17          | ~ (v1_funct_1 @ X20)
% 4.97/5.17          | ~ (v1_relat_1 @ X20))),
% 4.97/5.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.97/5.17  thf(redefinition_k6_partfun1, axiom,
% 4.97/5.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.97/5.17  thf('1', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('2', plain,
% 4.97/5.17      (![X20 : $i]:
% 4.97/5.17         (~ (v2_funct_1 @ X20)
% 4.97/5.17          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.17              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.17          | ~ (v1_funct_1 @ X20)
% 4.97/5.17          | ~ (v1_relat_1 @ X20))),
% 4.97/5.17      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.17  thf('3', plain,
% 4.97/5.17      (![X20 : $i]:
% 4.97/5.17         (~ (v2_funct_1 @ X20)
% 4.97/5.17          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 4.97/5.17              = (k6_relat_1 @ (k2_relat_1 @ X20)))
% 4.97/5.17          | ~ (v1_funct_1 @ X20)
% 4.97/5.17          | ~ (v1_relat_1 @ X20))),
% 4.97/5.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.97/5.17  thf('4', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('5', plain,
% 4.97/5.17      (![X20 : $i]:
% 4.97/5.17         (~ (v2_funct_1 @ X20)
% 4.97/5.17          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 4.97/5.17              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 4.97/5.17          | ~ (v1_funct_1 @ X20)
% 4.97/5.17          | ~ (v1_relat_1 @ X20))),
% 4.97/5.17      inference('demod', [status(thm)], ['3', '4'])).
% 4.97/5.17  thf(t36_funct_2, conjecture,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.97/5.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.97/5.17       ( ![D:$i]:
% 4.97/5.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.97/5.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.97/5.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.97/5.17               ( r2_relset_1 @
% 4.97/5.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.97/5.17                 ( k6_partfun1 @ A ) ) & 
% 4.97/5.17               ( v2_funct_1 @ C ) ) =>
% 4.97/5.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.97/5.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.97/5.17  thf(zf_stmt_0, negated_conjecture,
% 4.97/5.17    (~( ![A:$i,B:$i,C:$i]:
% 4.97/5.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.97/5.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.97/5.17          ( ![D:$i]:
% 4.97/5.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.97/5.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.97/5.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.97/5.17                  ( r2_relset_1 @
% 4.97/5.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.97/5.17                    ( k6_partfun1 @ A ) ) & 
% 4.97/5.17                  ( v2_funct_1 @ C ) ) =>
% 4.97/5.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.97/5.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 4.97/5.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 4.97/5.17  thf('6', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(t35_funct_2, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.97/5.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.97/5.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.97/5.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.97/5.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 4.97/5.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 4.97/5.17  thf('7', plain,
% 4.97/5.17      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.97/5.17         (((X64) = (k1_xboole_0))
% 4.97/5.17          | ~ (v1_funct_1 @ X65)
% 4.97/5.17          | ~ (v1_funct_2 @ X65 @ X66 @ X64)
% 4.97/5.17          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X64)))
% 4.97/5.17          | ((k5_relat_1 @ X65 @ (k2_funct_1 @ X65)) = (k6_partfun1 @ X66))
% 4.97/5.17          | ~ (v2_funct_1 @ X65)
% 4.97/5.17          | ((k2_relset_1 @ X66 @ X64 @ X65) != (X64)))),
% 4.97/5.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.97/5.17  thf('8', plain,
% 4.97/5.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 4.97/5.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ((sk_B) = (k1_xboole_0)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['6', '7'])).
% 4.97/5.17  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('13', plain,
% 4.97/5.17      ((((sk_B) != (sk_B))
% 4.97/5.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 4.97/5.17        | ((sk_B) = (k1_xboole_0)))),
% 4.97/5.17      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 4.97/5.17  thf('14', plain,
% 4.97/5.17      ((((sk_B) = (k1_xboole_0))
% 4.97/5.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 4.97/5.17      inference('simplify', [status(thm)], ['13'])).
% 4.97/5.17  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('16', plain,
% 4.97/5.17      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 4.97/5.17  thf(t55_relat_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( v1_relat_1 @ A ) =>
% 4.97/5.17       ( ![B:$i]:
% 4.97/5.17         ( ( v1_relat_1 @ B ) =>
% 4.97/5.17           ( ![C:$i]:
% 4.97/5.17             ( ( v1_relat_1 @ C ) =>
% 4.97/5.17               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 4.97/5.17                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.97/5.17  thf('17', plain,
% 4.97/5.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X4)
% 4.97/5.17          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.97/5.17              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 4.97/5.17          | ~ (v1_relat_1 @ X6)
% 4.97/5.17          | ~ (v1_relat_1 @ X5))),
% 4.97/5.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.97/5.17  thf('18', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ sk_C)
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.17      inference('sup+', [status(thm)], ['16', '17'])).
% 4.97/5.17  thf('19', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(cc2_relat_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( v1_relat_1 @ A ) =>
% 4.97/5.17       ( ![B:$i]:
% 4.97/5.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.97/5.17  thf('20', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 4.97/5.17          | (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X1))),
% 4.97/5.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.97/5.17  thf('21', plain,
% 4.97/5.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['19', '20'])).
% 4.97/5.17  thf(fc6_relat_1, axiom,
% 4.97/5.17    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.97/5.17  thf('22', plain,
% 4.97/5.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 4.97/5.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.97/5.17  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('24', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(redefinition_k2_relset_1, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.97/5.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.97/5.17  thf('25', plain,
% 4.97/5.17      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.97/5.17         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 4.97/5.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.97/5.17  thf('26', plain,
% 4.97/5.17      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['24', '25'])).
% 4.97/5.17  thf('27', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('28', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.17      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.17  thf(t80_relat_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( v1_relat_1 @ A ) =>
% 4.97/5.17       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 4.97/5.17  thf('29', plain,
% 4.97/5.17      (![X9 : $i]:
% 4.97/5.17         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.17          | ~ (v1_relat_1 @ X9))),
% 4.97/5.17      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.97/5.17  thf('30', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('31', plain,
% 4.97/5.17      (![X9 : $i]:
% 4.97/5.17         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.17          | ~ (v1_relat_1 @ X9))),
% 4.97/5.17      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.17  thf('32', plain,
% 4.97/5.17      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup+', [status(thm)], ['28', '31'])).
% 4.97/5.17  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('34', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.17      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.17  thf(t67_funct_1, axiom,
% 4.97/5.17    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 4.97/5.17  thf('35', plain,
% 4.97/5.17      (![X23 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X23)) = (k6_relat_1 @ X23))),
% 4.97/5.17      inference('cnf', [status(esa)], [t67_funct_1])).
% 4.97/5.17  thf('36', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('37', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('38', plain,
% 4.97/5.17      (![X23 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X23)) = (k6_partfun1 @ X23))),
% 4.97/5.17      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.97/5.17  thf(t66_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.17       ( ![B:$i]:
% 4.97/5.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.97/5.17           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 4.97/5.17             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 4.97/5.17               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 4.97/5.17  thf('39', plain,
% 4.97/5.17      (![X21 : $i, X22 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X21)
% 4.97/5.17          | ~ (v1_funct_1 @ X21)
% 4.97/5.17          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 4.97/5.17              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 4.97/5.17          | ~ (v2_funct_1 @ X21)
% 4.97/5.17          | ~ (v2_funct_1 @ X22)
% 4.97/5.17          | ~ (v1_funct_1 @ X22)
% 4.97/5.17          | ~ (v1_relat_1 @ X22))),
% 4.97/5.17      inference('cnf', [status(esa)], [t66_funct_1])).
% 4.97/5.17  thf('40', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 4.97/5.17            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_funct_1 @ X1)
% 4.97/5.17          | ~ (v2_funct_1 @ X1)
% 4.97/5.17          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 4.97/5.17          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 4.97/5.17          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 4.97/5.17      inference('sup+', [status(thm)], ['38', '39'])).
% 4.97/5.17  thf(fc4_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.97/5.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.97/5.17  thf('41', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 4.97/5.17      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.97/5.17  thf('42', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('43', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 4.97/5.17      inference('demod', [status(thm)], ['41', '42'])).
% 4.97/5.17  thf(fc3_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.97/5.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.97/5.17  thf('44', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 4.97/5.17      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.97/5.17  thf('45', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('46', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 4.97/5.17      inference('demod', [status(thm)], ['44', '45'])).
% 4.97/5.17  thf('47', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 4.97/5.17      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.97/5.17  thf('48', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.17  thf('49', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.17      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.17  thf('50', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 4.97/5.17            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_funct_1 @ X1)
% 4.97/5.17          | ~ (v2_funct_1 @ X1))),
% 4.97/5.17      inference('demod', [status(thm)], ['40', '43', '46', '49'])).
% 4.97/5.17  thf(dt_k2_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.17       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.97/5.17         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.97/5.17  thf('51', plain,
% 4.97/5.17      (![X10 : $i]:
% 4.97/5.17         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.97/5.17          | ~ (v1_funct_1 @ X10)
% 4.97/5.17          | ~ (v1_relat_1 @ X10))),
% 4.97/5.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.17  thf('52', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ (k2_funct_1 @ X0)))
% 4.97/5.17          | ~ (v2_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 4.97/5.17          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1))))),
% 4.97/5.17      inference('sup+', [status(thm)], ['50', '51'])).
% 4.97/5.17  thf('53', plain,
% 4.97/5.17      ((~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.17        | (v1_relat_1 @ 
% 4.97/5.17           (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))))),
% 4.97/5.17      inference('sup-', [status(thm)], ['34', '52'])).
% 4.97/5.17  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('55', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.17      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.17  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('60', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.17      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.17  thf('61', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 4.97/5.17            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_funct_1 @ X1)
% 4.97/5.17          | ~ (v2_funct_1 @ X1))),
% 4.97/5.17      inference('demod', [status(thm)], ['40', '43', '46', '49'])).
% 4.97/5.17  thf('62', plain,
% 4.97/5.17      ((((k2_funct_1 @ sk_C)
% 4.97/5.17          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup+', [status(thm)], ['60', '61'])).
% 4.97/5.17  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('66', plain,
% 4.97/5.17      (((k2_funct_1 @ sk_C)
% 4.97/5.17         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))),
% 4.97/5.17      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 4.97/5.17  thf('67', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.17      inference('demod', [status(thm)],
% 4.97/5.17                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.17  thf('68', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('demod', [status(thm)], ['18', '23', '67'])).
% 4.97/5.17  thf('69', plain,
% 4.97/5.17      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C)
% 4.97/5.17          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup+', [status(thm)], ['5', '68'])).
% 4.97/5.17  thf('70', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.17      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.17  thf('71', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.17      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.17  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('76', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 4.97/5.17      inference('demod', [status(thm)],
% 4.97/5.17                ['69', '70', '71', '72', '73', '74', '75'])).
% 4.97/5.17  thf('77', plain,
% 4.97/5.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.97/5.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.97/5.17        (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('78', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(t24_funct_2, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.97/5.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.97/5.17       ( ![D:$i]:
% 4.97/5.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.97/5.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.97/5.17           ( ( r2_relset_1 @
% 4.97/5.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.97/5.17               ( k6_partfun1 @ B ) ) =>
% 4.97/5.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.97/5.17  thf('79', plain,
% 4.97/5.17      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 4.97/5.17         (~ (v1_funct_1 @ X57)
% 4.97/5.17          | ~ (v1_funct_2 @ X57 @ X58 @ X59)
% 4.97/5.17          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 4.97/5.17          | ~ (r2_relset_1 @ X58 @ X58 @ 
% 4.97/5.17               (k1_partfun1 @ X58 @ X59 @ X59 @ X58 @ X57 @ X60) @ 
% 4.97/5.17               (k6_partfun1 @ X58))
% 4.97/5.17          | ((k2_relset_1 @ X59 @ X58 @ X60) = (X58))
% 4.97/5.17          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58)))
% 4.97/5.17          | ~ (v1_funct_2 @ X60 @ X59 @ X58)
% 4.97/5.17          | ~ (v1_funct_1 @ X60))),
% 4.97/5.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.97/5.17  thf('80', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.97/5.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.97/5.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.97/5.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.97/5.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 4.97/5.17               (k6_partfun1 @ sk_A))
% 4.97/5.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.97/5.17          | ~ (v1_funct_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['78', '79'])).
% 4.97/5.17  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('83', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.97/5.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.97/5.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.97/5.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.97/5.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 4.97/5.17               (k6_partfun1 @ sk_A)))),
% 4.97/5.17      inference('demod', [status(thm)], ['80', '81', '82'])).
% 4.97/5.17  thf('84', plain,
% 4.97/5.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 4.97/5.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.97/5.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_D))),
% 4.97/5.17      inference('sup-', [status(thm)], ['77', '83'])).
% 4.97/5.17  thf('85', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('86', plain,
% 4.97/5.17      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.97/5.17         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 4.97/5.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.97/5.17  thf('87', plain,
% 4.97/5.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup-', [status(thm)], ['85', '86'])).
% 4.97/5.17  thf('88', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('89', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('91', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.97/5.17      inference('demod', [status(thm)], ['84', '87', '88', '89', '90'])).
% 4.97/5.17  thf('92', plain,
% 4.97/5.17      (![X9 : $i]:
% 4.97/5.17         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.17          | ~ (v1_relat_1 @ X9))),
% 4.97/5.17      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.17  thf('93', plain,
% 4.97/5.17      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup+', [status(thm)], ['91', '92'])).
% 4.97/5.17  thf('94', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('95', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 4.97/5.17          | (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X1))),
% 4.97/5.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.97/5.17  thf('96', plain,
% 4.97/5.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup-', [status(thm)], ['94', '95'])).
% 4.97/5.17  thf('97', plain,
% 4.97/5.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 4.97/5.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.97/5.17  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.17      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.17  thf('99', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['93', '98'])).
% 4.97/5.17  thf('100', plain,
% 4.97/5.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X4)
% 4.97/5.17          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.97/5.17              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 4.97/5.17          | ~ (v1_relat_1 @ X6)
% 4.97/5.17          | ~ (v1_relat_1 @ X5))),
% 4.97/5.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.97/5.17  thf('101', plain,
% 4.97/5.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X4)
% 4.97/5.17          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.97/5.17              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 4.97/5.17          | ~ (v1_relat_1 @ X6)
% 4.97/5.17          | ~ (v1_relat_1 @ X5))),
% 4.97/5.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.97/5.17  thf('102', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 4.97/5.17            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 4.97/5.17          | ~ (v1_relat_1 @ X2)
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 4.97/5.17          | ~ (v1_relat_1 @ X3)
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('sup+', [status(thm)], ['100', '101'])).
% 4.97/5.17  thf('103', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X3)
% 4.97/5.17          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X2)
% 4.97/5.17          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 4.97/5.17              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 4.97/5.17      inference('simplify', [status(thm)], ['102'])).
% 4.97/5.17  thf('104', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ sk_D)
% 4.97/5.17          | ((k5_relat_1 @ 
% 4.97/5.17              (k5_relat_1 @ sk_D @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ X1)) @ 
% 4.97/5.17              X0)
% 4.97/5.17              = (k5_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) @ 
% 4.97/5.17                 (k5_relat_1 @ X1 @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ sk_D)
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('sup-', [status(thm)], ['99', '103'])).
% 4.97/5.17  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.17      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.17  thf('106', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['93', '98'])).
% 4.97/5.17  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.17      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.17  thf('108', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.17      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.17  thf('109', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i]:
% 4.97/5.17         (((k5_relat_1 @ 
% 4.97/5.17            (k5_relat_1 @ sk_D @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ X1)) @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ X1 @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ X1)
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 4.97/5.17  thf('110', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup+', [status(thm)], ['76', '109'])).
% 4.97/5.17  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('112', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('demod', [status(thm)], ['110', '111'])).
% 4.97/5.17  thf('113', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('114', plain,
% 4.97/5.17      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.97/5.17         (((X64) = (k1_xboole_0))
% 4.97/5.17          | ~ (v1_funct_1 @ X65)
% 4.97/5.17          | ~ (v1_funct_2 @ X65 @ X66 @ X64)
% 4.97/5.17          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X64)))
% 4.97/5.17          | ((k5_relat_1 @ X65 @ (k2_funct_1 @ X65)) = (k6_partfun1 @ X66))
% 4.97/5.17          | ~ (v2_funct_1 @ X65)
% 4.97/5.17          | ((k2_relset_1 @ X66 @ X64 @ X65) != (X64)))),
% 4.97/5.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.97/5.17  thf('115', plain,
% 4.97/5.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D)
% 4.97/5.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 4.97/5.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_D)
% 4.97/5.17        | ((sk_A) = (k1_xboole_0)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['113', '114'])).
% 4.97/5.17  thf('116', plain,
% 4.97/5.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup-', [status(thm)], ['85', '86'])).
% 4.97/5.17  thf('117', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('119', plain,
% 4.97/5.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D)
% 4.97/5.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 4.97/5.17        | ((sk_A) = (k1_xboole_0)))),
% 4.97/5.17      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 4.97/5.17  thf('120', plain, (((sk_A) != (k1_xboole_0))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('121', plain,
% 4.97/5.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D)
% 4.97/5.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 4.97/5.17      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 4.97/5.17  thf('122', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.97/5.17      inference('demod', [status(thm)], ['84', '87', '88', '89', '90'])).
% 4.97/5.17  thf('123', plain,
% 4.97/5.17      ((((sk_A) != (sk_A))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D)
% 4.97/5.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 4.97/5.17      inference('demod', [status(thm)], ['121', '122'])).
% 4.97/5.17  thf('124', plain,
% 4.97/5.17      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D))),
% 4.97/5.17      inference('simplify', [status(thm)], ['123'])).
% 4.97/5.17  thf('125', plain,
% 4.97/5.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.97/5.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.97/5.17        (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('126', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('127', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(redefinition_k1_partfun1, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.97/5.17     ( ( ( v1_funct_1 @ E ) & 
% 4.97/5.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.97/5.17         ( v1_funct_1 @ F ) & 
% 4.97/5.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.97/5.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.97/5.17  thf('128', plain,
% 4.97/5.17      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 4.97/5.17         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 4.97/5.17          | ~ (v1_funct_1 @ X50)
% 4.97/5.17          | ~ (v1_funct_1 @ X53)
% 4.97/5.17          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 4.97/5.17          | ((k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53)
% 4.97/5.17              = (k5_relat_1 @ X50 @ X53)))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.97/5.17  thf('129', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_C @ X0))
% 4.97/5.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['127', '128'])).
% 4.97/5.17  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('131', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.97/5.17            = (k5_relat_1 @ sk_C @ X0))
% 4.97/5.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.97/5.17          | ~ (v1_funct_1 @ X0))),
% 4.97/5.17      inference('demod', [status(thm)], ['129', '130'])).
% 4.97/5.17  thf('132', plain,
% 4.97/5.17      ((~ (v1_funct_1 @ sk_D)
% 4.97/5.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.97/5.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['126', '131'])).
% 4.97/5.17  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('134', plain,
% 4.97/5.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.97/5.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['132', '133'])).
% 4.97/5.17  thf('135', plain,
% 4.97/5.17      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.97/5.17        (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('demod', [status(thm)], ['125', '134'])).
% 4.97/5.17  thf('136', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('137', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(dt_k1_partfun1, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.97/5.17     ( ( ( v1_funct_1 @ E ) & 
% 4.97/5.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.97/5.17         ( v1_funct_1 @ F ) & 
% 4.97/5.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.97/5.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.97/5.17         ( m1_subset_1 @
% 4.97/5.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.97/5.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.97/5.17  thf('138', plain,
% 4.97/5.17      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 4.97/5.17         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.97/5.17          | ~ (v1_funct_1 @ X42)
% 4.97/5.17          | ~ (v1_funct_1 @ X45)
% 4.97/5.17          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.97/5.17          | (m1_subset_1 @ (k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45) @ 
% 4.97/5.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X47))))),
% 4.97/5.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.97/5.17  thf('139', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.97/5.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.97/5.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.97/5.17          | ~ (v1_funct_1 @ X1)
% 4.97/5.17          | ~ (v1_funct_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['137', '138'])).
% 4.97/5.17  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('141', plain,
% 4.97/5.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.97/5.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.97/5.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.97/5.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.97/5.17          | ~ (v1_funct_1 @ X1))),
% 4.97/5.17      inference('demod', [status(thm)], ['139', '140'])).
% 4.97/5.17  thf('142', plain,
% 4.97/5.17      ((~ (v1_funct_1 @ sk_D)
% 4.97/5.17        | (m1_subset_1 @ 
% 4.97/5.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.97/5.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.97/5.17      inference('sup-', [status(thm)], ['136', '141'])).
% 4.97/5.17  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('144', plain,
% 4.97/5.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.97/5.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['132', '133'])).
% 4.97/5.17  thf('145', plain,
% 4.97/5.17      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.97/5.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.97/5.17      inference('demod', [status(thm)], ['142', '143', '144'])).
% 4.97/5.17  thf(redefinition_r2_relset_1, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i,D:$i]:
% 4.97/5.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.97/5.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.97/5.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.97/5.17  thf('146', plain,
% 4.97/5.17      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.97/5.17         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.97/5.17          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.97/5.17          | ((X30) = (X33))
% 4.97/5.17          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.97/5.17  thf('147', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.97/5.17          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.97/5.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.97/5.17      inference('sup-', [status(thm)], ['145', '146'])).
% 4.97/5.17  thf('148', plain,
% 4.97/5.17      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.97/5.17        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['135', '147'])).
% 4.97/5.17  thf(dt_k6_partfun1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( m1_subset_1 @
% 4.97/5.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.97/5.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.97/5.17  thf('149', plain,
% 4.97/5.17      (![X49 : $i]:
% 4.97/5.17         (m1_subset_1 @ (k6_partfun1 @ X49) @ 
% 4.97/5.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X49)))),
% 4.97/5.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.97/5.17  thf('150', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('demod', [status(thm)], ['148', '149'])).
% 4.97/5.17  thf(t48_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.17       ( ![B:$i]:
% 4.97/5.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.97/5.17           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 4.97/5.17               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 4.97/5.17             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 4.97/5.17  thf('151', plain,
% 4.97/5.17      (![X16 : $i, X17 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X16)
% 4.97/5.17          | ~ (v1_funct_1 @ X16)
% 4.97/5.17          | (v2_funct_1 @ X17)
% 4.97/5.17          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 4.97/5.17          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 4.97/5.17          | ~ (v1_funct_1 @ X17)
% 4.97/5.17          | ~ (v1_relat_1 @ X17))),
% 4.97/5.17      inference('cnf', [status(esa)], [t48_funct_1])).
% 4.97/5.17  thf('152', plain,
% 4.97/5.17      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_D)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_D)
% 4.97/5.17        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 4.97/5.17        | (v2_funct_1 @ sk_D)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup-', [status(thm)], ['150', '151'])).
% 4.97/5.17  thf('153', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 4.97/5.17      inference('demod', [status(thm)], ['41', '42'])).
% 4.97/5.17  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.17      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.17  thf('155', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.17      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.17  thf('157', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(d1_funct_2, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.97/5.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.97/5.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.97/5.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.97/5.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.97/5.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.97/5.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.97/5.17  thf(zf_stmt_1, axiom,
% 4.97/5.17    (![C:$i,B:$i,A:$i]:
% 4.97/5.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.97/5.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.97/5.17  thf('158', plain,
% 4.97/5.17      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.97/5.17         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 4.97/5.17          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 4.97/5.17          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.97/5.17  thf('159', plain,
% 4.97/5.17      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 4.97/5.17        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['157', '158'])).
% 4.97/5.17  thf(zf_stmt_2, axiom,
% 4.97/5.17    (![B:$i,A:$i]:
% 4.97/5.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.97/5.17       ( zip_tseitin_0 @ B @ A ) ))).
% 4.97/5.17  thf('160', plain,
% 4.97/5.17      (![X34 : $i, X35 : $i]:
% 4.97/5.17         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.97/5.17  thf('161', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.97/5.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.97/5.17  thf(zf_stmt_5, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.97/5.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.97/5.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.97/5.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.97/5.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.97/5.17  thf('162', plain,
% 4.97/5.17      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.97/5.17         (~ (zip_tseitin_0 @ X39 @ X40)
% 4.97/5.17          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 4.97/5.17          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.97/5.17  thf('163', plain,
% 4.97/5.17      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 4.97/5.17      inference('sup-', [status(thm)], ['161', '162'])).
% 4.97/5.17  thf('164', plain,
% 4.97/5.17      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 4.97/5.17      inference('sup-', [status(thm)], ['160', '163'])).
% 4.97/5.17  thf('165', plain, (((sk_A) != (k1_xboole_0))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('166', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 4.97/5.17      inference('simplify_reflect-', [status(thm)], ['164', '165'])).
% 4.97/5.17  thf('167', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf(redefinition_k1_relset_1, axiom,
% 4.97/5.17    (![A:$i,B:$i,C:$i]:
% 4.97/5.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.97/5.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.97/5.17  thf('168', plain,
% 4.97/5.17      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.97/5.17         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 4.97/5.17          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.97/5.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.97/5.17  thf('169', plain,
% 4.97/5.17      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup-', [status(thm)], ['167', '168'])).
% 4.97/5.17  thf('170', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['159', '166', '169'])).
% 4.97/5.17  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('173', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)],
% 4.97/5.17                ['152', '153', '154', '155', '156', '170', '171', '172'])).
% 4.97/5.17  thf('174', plain, ((v2_funct_1 @ sk_D)),
% 4.97/5.17      inference('simplify', [status(thm)], ['173'])).
% 4.97/5.17  thf('175', plain,
% 4.97/5.17      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 4.97/5.17      inference('demod', [status(thm)], ['124', '174'])).
% 4.97/5.17  thf('176', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['159', '166', '169'])).
% 4.97/5.17  thf('177', plain,
% 4.97/5.17      (![X10 : $i]:
% 4.97/5.17         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.97/5.17          | ~ (v1_funct_1 @ X10)
% 4.97/5.17          | ~ (v1_relat_1 @ X10))),
% 4.97/5.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.17  thf(t55_funct_1, axiom,
% 4.97/5.17    (![A:$i]:
% 4.97/5.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.17       ( ( v2_funct_1 @ A ) =>
% 4.97/5.17         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.97/5.17           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.97/5.17  thf('178', plain,
% 4.97/5.17      (![X18 : $i]:
% 4.97/5.17         (~ (v2_funct_1 @ X18)
% 4.97/5.17          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 4.97/5.17          | ~ (v1_funct_1 @ X18)
% 4.97/5.17          | ~ (v1_relat_1 @ X18))),
% 4.97/5.17      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.97/5.17  thf('179', plain,
% 4.97/5.17      (![X9 : $i]:
% 4.97/5.17         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.17          | ~ (v1_relat_1 @ X9))),
% 4.97/5.17      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.17  thf('180', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 4.97/5.17            = (k2_funct_1 @ X0))
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v2_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.97/5.17      inference('sup+', [status(thm)], ['178', '179'])).
% 4.97/5.17  thf('181', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v2_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 4.97/5.17              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['177', '180'])).
% 4.97/5.17  thf('182', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 4.97/5.17            = (k2_funct_1 @ X0))
% 4.97/5.17          | ~ (v2_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_funct_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('simplify', [status(thm)], ['181'])).
% 4.97/5.17  thf('183', plain,
% 4.97/5.17      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ sk_B))
% 4.97/5.17          = (k2_funct_1 @ sk_D))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_D)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_D)
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D))),
% 4.97/5.17      inference('sup+', [status(thm)], ['176', '182'])).
% 4.97/5.17  thf('184', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.17      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.17  thf('185', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('186', plain,
% 4.97/5.17      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ sk_B))
% 4.97/5.17          = (k2_funct_1 @ sk_D))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['183', '184', '185'])).
% 4.97/5.17  thf('187', plain, ((v2_funct_1 @ sk_D)),
% 4.97/5.17      inference('simplify', [status(thm)], ['173'])).
% 4.97/5.17  thf('188', plain,
% 4.97/5.17      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ sk_B))
% 4.97/5.17         = (k2_funct_1 @ sk_D))),
% 4.97/5.17      inference('demod', [status(thm)], ['186', '187'])).
% 4.97/5.17  thf('189', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.97/5.17      inference('demod', [status(thm)], ['148', '149'])).
% 4.97/5.17  thf('190', plain,
% 4.97/5.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('191', plain,
% 4.97/5.17      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.97/5.17         (((X64) = (k1_xboole_0))
% 4.97/5.17          | ~ (v1_funct_1 @ X65)
% 4.97/5.17          | ~ (v1_funct_2 @ X65 @ X66 @ X64)
% 4.97/5.17          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X64)))
% 4.97/5.17          | ((k5_relat_1 @ (k2_funct_1 @ X65) @ X65) = (k6_partfun1 @ X64))
% 4.97/5.17          | ~ (v2_funct_1 @ X65)
% 4.97/5.17          | ((k2_relset_1 @ X66 @ X64 @ X65) != (X64)))),
% 4.97/5.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.97/5.17  thf('192', plain,
% 4.97/5.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.97/5.17        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 4.97/5.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.97/5.17        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.17        | ((sk_B) = (k1_xboole_0)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['190', '191'])).
% 4.97/5.17  thf('193', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('195', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('197', plain,
% 4.97/5.17      ((((sk_B) != (sk_B))
% 4.97/5.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 4.97/5.17        | ((sk_B) = (k1_xboole_0)))),
% 4.97/5.17      inference('demod', [status(thm)], ['192', '193', '194', '195', '196'])).
% 4.97/5.17  thf('198', plain,
% 4.97/5.17      ((((sk_B) = (k1_xboole_0))
% 4.97/5.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 4.97/5.17      inference('simplify', [status(thm)], ['197'])).
% 4.97/5.17  thf('199', plain, (((sk_B) != (k1_xboole_0))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('200', plain,
% 4.97/5.17      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 4.97/5.17      inference('simplify_reflect-', [status(thm)], ['198', '199'])).
% 4.97/5.17  thf('201', plain,
% 4.97/5.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.97/5.17         (~ (v1_relat_1 @ X4)
% 4.97/5.17          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.97/5.17              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 4.97/5.17          | ~ (v1_relat_1 @ X6)
% 4.97/5.17          | ~ (v1_relat_1 @ X5))),
% 4.97/5.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.97/5.17  thf('202', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.97/5.17            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.17          | ~ (v1_relat_1 @ X0)
% 4.97/5.17          | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.17      inference('sup+', [status(thm)], ['200', '201'])).
% 4.97/5.17  thf('203', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.17      inference('demod', [status(thm)],
% 4.97/5.17                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.17  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.17      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.17  thf('205', plain,
% 4.97/5.17      (![X0 : $i]:
% 4.97/5.17         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.97/5.17            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.97/5.17          | ~ (v1_relat_1 @ X0))),
% 4.97/5.17      inference('demod', [status(thm)], ['202', '203', '204'])).
% 4.97/5.17  thf('206', plain,
% 4.97/5.17      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 4.97/5.17          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 4.97/5.17        | ~ (v1_relat_1 @ sk_D))),
% 4.97/5.17      inference('sup+', [status(thm)], ['189', '205'])).
% 4.97/5.17  thf('207', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.17  thf('208', plain,
% 4.97/5.17      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.97/5.17         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 4.97/5.17          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 4.97/5.17          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 4.97/5.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.97/5.17  thf('209', plain,
% 4.97/5.17      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 4.97/5.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 4.97/5.17      inference('sup-', [status(thm)], ['207', '208'])).
% 4.97/5.17  thf('210', plain,
% 4.97/5.17      (![X34 : $i, X35 : $i]:
% 4.97/5.17         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.97/5.18  thf('211', plain,
% 4.97/5.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('212', plain,
% 4.97/5.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.97/5.18         (~ (zip_tseitin_0 @ X39 @ X40)
% 4.97/5.18          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 4.97/5.18          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.97/5.18  thf('213', plain,
% 4.97/5.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.97/5.18      inference('sup-', [status(thm)], ['211', '212'])).
% 4.97/5.18  thf('214', plain,
% 4.97/5.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.97/5.18      inference('sup-', [status(thm)], ['210', '213'])).
% 4.97/5.18  thf('215', plain, (((sk_B) != (k1_xboole_0))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('216', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 4.97/5.18      inference('simplify_reflect-', [status(thm)], ['214', '215'])).
% 4.97/5.18  thf('217', plain,
% 4.97/5.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('218', plain,
% 4.97/5.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.97/5.18         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 4.97/5.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.97/5.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.97/5.18  thf('219', plain,
% 4.97/5.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('sup-', [status(thm)], ['217', '218'])).
% 4.97/5.18  thf('220', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf('221', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 4.97/5.18            = (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0))),
% 4.97/5.18      inference('simplify', [status(thm)], ['181'])).
% 4.97/5.18  thf('222', plain,
% 4.97/5.18      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 4.97/5.18          = (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C))),
% 4.97/5.18      inference('sup+', [status(thm)], ['220', '221'])).
% 4.97/5.18  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('225', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('226', plain,
% 4.97/5.18      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 4.97/5.18         = (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 4.97/5.18  thf('227', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.18      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.18  thf('228', plain,
% 4.97/5.18      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['206', '226', '227'])).
% 4.97/5.18  thf('229', plain,
% 4.97/5.18      (![X23 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X23)) = (k6_partfun1 @ X23))),
% 4.97/5.18      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.97/5.18  thf('230', plain,
% 4.97/5.18      (![X21 : $i, X22 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X21)
% 4.97/5.18          | ~ (v1_funct_1 @ X21)
% 4.97/5.18          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 4.97/5.18              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 4.97/5.18          | ~ (v2_funct_1 @ X21)
% 4.97/5.18          | ~ (v2_funct_1 @ X22)
% 4.97/5.18          | ~ (v1_funct_1 @ X22)
% 4.97/5.18          | ~ (v1_relat_1 @ X22))),
% 4.97/5.18      inference('cnf', [status(esa)], [t66_funct_1])).
% 4.97/5.18  thf('231', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 4.97/5.18            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 4.97/5.18          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 4.97/5.18          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ X1))),
% 4.97/5.18      inference('sup+', [status(thm)], ['229', '230'])).
% 4.97/5.18  thf('232', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('233', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 4.97/5.18      inference('demod', [status(thm)], ['44', '45'])).
% 4.97/5.18  thf('234', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 4.97/5.18      inference('demod', [status(thm)], ['41', '42'])).
% 4.97/5.18  thf('235', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 4.97/5.18            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 4.97/5.18          | ~ (v2_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ X1))),
% 4.97/5.18      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 4.97/5.18  thf('236', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18          = (k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ sk_B)))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_D)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_D)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_D))),
% 4.97/5.18      inference('sup+', [status(thm)], ['228', '235'])).
% 4.97/5.18  thf('237', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.18  thf('238', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 4.97/5.18            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 4.97/5.18          | ~ (v1_relat_1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)], ['18', '23', '67'])).
% 4.97/5.18  thf('239', plain,
% 4.97/5.18      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18          (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18          = (k5_relat_1 @ sk_C @ 
% 4.97/5.18             (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('sup+', [status(thm)], ['237', '238'])).
% 4.97/5.18  thf('240', plain,
% 4.97/5.18      (![X10 : $i]:
% 4.97/5.18         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.97/5.18          | ~ (v1_funct_1 @ X10)
% 4.97/5.18          | ~ (v1_relat_1 @ X10))),
% 4.97/5.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.18  thf('241', plain,
% 4.97/5.18      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 4.97/5.18         = (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 4.97/5.18  thf('242', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 4.97/5.18            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 4.97/5.18          | ~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v1_funct_1 @ X1)
% 4.97/5.18          | ~ (v2_funct_1 @ X1))),
% 4.97/5.18      inference('demod', [status(thm)], ['40', '43', '46', '49'])).
% 4.97/5.18  thf('243', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18             (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 4.97/5.18        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup+', [status(thm)], ['241', '242'])).
% 4.97/5.18  thf('244', plain,
% 4.97/5.18      (![X18 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X18)
% 4.97/5.18          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 4.97/5.18          | ~ (v1_funct_1 @ X18)
% 4.97/5.18          | ~ (v1_relat_1 @ X18))),
% 4.97/5.18      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.97/5.18  thf('245', plain,
% 4.97/5.18      (![X10 : $i]:
% 4.97/5.18         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.97/5.18          | ~ (v1_funct_1 @ X10)
% 4.97/5.18          | ~ (v1_relat_1 @ X10))),
% 4.97/5.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.18  thf('246', plain,
% 4.97/5.18      (![X10 : $i]:
% 4.97/5.18         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.97/5.18          | ~ (v1_funct_1 @ X10)
% 4.97/5.18          | ~ (v1_relat_1 @ X10))),
% 4.97/5.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.18  thf('247', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.18  thf('248', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.18  thf('249', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.18  thf('250', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf(t58_funct_1, axiom,
% 4.97/5.18    (![A:$i]:
% 4.97/5.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.97/5.18       ( ( v2_funct_1 @ A ) =>
% 4.97/5.18         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 4.97/5.18             ( k1_relat_1 @ A ) ) & 
% 4.97/5.18           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 4.97/5.18             ( k1_relat_1 @ A ) ) ) ) ))).
% 4.97/5.18  thf('251', plain,
% 4.97/5.18      (![X19 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X19)
% 4.97/5.18          | ((k2_relat_1 @ (k5_relat_1 @ X19 @ (k2_funct_1 @ X19)))
% 4.97/5.18              = (k1_relat_1 @ X19))
% 4.97/5.18          | ~ (v1_funct_1 @ X19)
% 4.97/5.18          | ~ (v1_relat_1 @ X19))),
% 4.97/5.18      inference('cnf', [status(esa)], [t58_funct_1])).
% 4.97/5.18  thf('252', plain,
% 4.97/5.18      (![X9 : $i]:
% 4.97/5.18         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.18          | ~ (v1_relat_1 @ X9))),
% 4.97/5.18      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.18  thf('253', plain,
% 4.97/5.18      (![X9 : $i]:
% 4.97/5.18         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.18          | ~ (v1_relat_1 @ X9))),
% 4.97/5.18      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.18  thf('254', plain,
% 4.97/5.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X4)
% 4.97/5.18          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.97/5.18              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 4.97/5.18          | ~ (v1_relat_1 @ X6)
% 4.97/5.18          | ~ (v1_relat_1 @ X5))),
% 4.97/5.18      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.97/5.18  thf('255', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k5_relat_1 @ X0 @ X1)
% 4.97/5.18            = (k5_relat_1 @ X0 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 4.97/5.18      inference('sup+', [status(thm)], ['253', '254'])).
% 4.97/5.18  thf('256', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('257', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k5_relat_1 @ X0 @ X1)
% 4.97/5.18            = (k5_relat_1 @ X0 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X1))),
% 4.97/5.18      inference('demod', [status(thm)], ['255', '256'])).
% 4.97/5.18  thf('258', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ((k5_relat_1 @ X0 @ X1)
% 4.97/5.18              = (k5_relat_1 @ X0 @ 
% 4.97/5.18                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1))))),
% 4.97/5.18      inference('simplify', [status(thm)], ['257'])).
% 4.97/5.18  thf('259', plain,
% 4.97/5.18      (![X16 : $i, X17 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X16)
% 4.97/5.18          | ~ (v1_funct_1 @ X16)
% 4.97/5.18          | (v2_funct_1 @ X16)
% 4.97/5.18          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 4.97/5.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 4.97/5.18          | ~ (v1_funct_1 @ X17)
% 4.97/5.18          | ~ (v1_relat_1 @ X17))),
% 4.97/5.18      inference('cnf', [status(esa)], [t48_funct_1])).
% 4.97/5.18  thf('260', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0))
% 4.97/5.18          | ~ (v1_funct_1 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0))
% 4.97/5.18          | ((k2_relat_1 @ X1)
% 4.97/5.18              != (k1_relat_1 @ 
% 4.97/5.18                  (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0)))
% 4.97/5.18          | (v2_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_funct_1 @ X1)
% 4.97/5.18          | ~ (v1_relat_1 @ X1))),
% 4.97/5.18      inference('sup-', [status(thm)], ['258', '259'])).
% 4.97/5.18  thf('261', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (~ (v1_funct_1 @ X1)
% 4.97/5.18          | (v2_funct_1 @ X1)
% 4.97/5.18          | ((k2_relat_1 @ X1)
% 4.97/5.18              != (k1_relat_1 @ 
% 4.97/5.18                  (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0)))
% 4.97/5.18          | ~ (v1_funct_1 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 4.97/5.18      inference('simplify', [status(thm)], ['260'])).
% 4.97/5.18  thf('262', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 4.97/5.18          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 4.97/5.18          | ~ (v2_funct_1 @ 
% 4.97/5.18               (k5_relat_1 @ X0 @ 
% 4.97/5.18                (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ 
% 4.97/5.18               (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 4.97/5.18          | ~ (v1_relat_1 @ 
% 4.97/5.18               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 4.97/5.18                (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))
% 4.97/5.18          | ((k2_relat_1 @ X0)
% 4.97/5.18              != (k1_relat_1 @ 
% 4.97/5.18                  (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 4.97/5.18                   (k6_partfun1 @ 
% 4.97/5.18                    (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))))
% 4.97/5.18          | (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0))),
% 4.97/5.18      inference('sup-', [status(thm)], ['252', '261'])).
% 4.97/5.18  thf('263', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 4.97/5.18      inference('demod', [status(thm)], ['44', '45'])).
% 4.97/5.18  thf('264', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf(t71_relat_1, axiom,
% 4.97/5.18    (![A:$i]:
% 4.97/5.18     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.97/5.18       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.97/5.18  thf('265', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 4.97/5.18      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.97/5.18  thf('266', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.18  thf('267', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 4.97/5.18      inference('demod', [status(thm)], ['265', '266'])).
% 4.97/5.18  thf('268', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 4.97/5.18      inference('demod', [status(thm)], ['265', '266'])).
% 4.97/5.18  thf('269', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('270', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 4.97/5.18      inference('demod', [status(thm)], ['265', '266'])).
% 4.97/5.18  thf('271', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 4.97/5.18      inference('demod', [status(thm)], ['265', '266'])).
% 4.97/5.18  thf('272', plain,
% 4.97/5.18      (![X9 : $i]:
% 4.97/5.18         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 4.97/5.18          | ~ (v1_relat_1 @ X9))),
% 4.97/5.18      inference('demod', [status(thm)], ['29', '30'])).
% 4.97/5.18  thf('273', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.97/5.18            = (k6_partfun1 @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 4.97/5.18      inference('sup+', [status(thm)], ['271', '272'])).
% 4.97/5.18  thf('274', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('275', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.97/5.18           = (k6_partfun1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)], ['273', '274'])).
% 4.97/5.18  thf('276', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('277', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 4.97/5.18      inference('demod', [status(thm)], ['265', '266'])).
% 4.97/5.18  thf('278', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.97/5.18           = (k6_partfun1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)], ['273', '274'])).
% 4.97/5.18  thf('279', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 4.97/5.18      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.97/5.18  thf('280', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 4.97/5.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.97/5.18  thf('281', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 4.97/5.18      inference('demod', [status(thm)], ['279', '280'])).
% 4.97/5.18  thf('282', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 4.97/5.18          | (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['262', '263', '264', '267', '268', '269', '270', '275', 
% 4.97/5.18                 '276', '277', '278', '281'])).
% 4.97/5.18  thf('283', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (~ (v1_funct_1 @ X0)
% 4.97/5.18          | (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v2_funct_1 @ 
% 4.97/5.18               (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 4.97/5.18      inference('simplify', [status(thm)], ['282'])).
% 4.97/5.18  thf('284', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ 
% 4.97/5.18             (k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 4.97/5.18              (k6_partfun1 @ (k1_relat_1 @ X0))))
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 4.97/5.18          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 4.97/5.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['251', '283'])).
% 4.97/5.18  thf('285', plain,
% 4.97/5.18      ((~ (v2_funct_1 @ 
% 4.97/5.18           (k5_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) @ 
% 4.97/5.18            (k6_partfun1 @ sk_A)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.18      inference('sup-', [status(thm)], ['250', '284'])).
% 4.97/5.18  thf('286', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('287', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('288', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('289', plain,
% 4.97/5.18      ((~ (v2_funct_1 @ 
% 4.97/5.18           (k5_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) @ 
% 4.97/5.18            (k6_partfun1 @ sk_A)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)], ['285', '286', '287', '288'])).
% 4.97/5.18  thf('290', plain,
% 4.97/5.18      ((~ (v2_funct_1 @ 
% 4.97/5.18           (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 4.97/5.18            (k6_partfun1 @ sk_A)))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['249', '289'])).
% 4.97/5.18  thf('291', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf('292', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 4.97/5.18           = (k6_partfun1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)], ['273', '274'])).
% 4.97/5.18  thf('293', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 4.97/5.18      inference('demod', [status(thm)], ['41', '42'])).
% 4.97/5.18  thf('294', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('295', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('296', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('297', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['290', '291', '292', '293', '294', '295', '296'])).
% 4.97/5.18  thf('298', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['248', '297'])).
% 4.97/5.18  thf('299', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf('300', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 4.97/5.18      inference('demod', [status(thm)], ['47', '48'])).
% 4.97/5.18  thf('301', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('302', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('303', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('304', plain,
% 4.97/5.18      ((~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['298', '299', '300', '301', '302', '303'])).
% 4.97/5.18  thf('305', plain,
% 4.97/5.18      ((~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['247', '304'])).
% 4.97/5.18  thf('306', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf('307', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 4.97/5.18      inference('demod', [status(thm)], ['44', '45'])).
% 4.97/5.18  thf('308', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('309', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('310', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('311', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['305', '306', '307', '308', '309', '310'])).
% 4.97/5.18  thf('312', plain,
% 4.97/5.18      (![X16 : $i, X17 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X16)
% 4.97/5.18          | ~ (v1_funct_1 @ X16)
% 4.97/5.18          | (v2_funct_1 @ X17)
% 4.97/5.18          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 4.97/5.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 4.97/5.18          | ~ (v1_funct_1 @ X17)
% 4.97/5.18          | ~ (v1_relat_1 @ X17))),
% 4.97/5.18      inference('cnf', [status(esa)], [t48_funct_1])).
% 4.97/5.18  thf('313', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.18      inference('sup-', [status(thm)], ['311', '312'])).
% 4.97/5.18  thf('314', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.18      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.18  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('316', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('317', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['313', '314', '315', '316'])).
% 4.97/5.18  thf('318', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup-', [status(thm)], ['246', '317'])).
% 4.97/5.18  thf('319', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('320', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('321', plain,
% 4.97/5.18      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['318', '319', '320'])).
% 4.97/5.18  thf('322', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup-', [status(thm)], ['245', '321'])).
% 4.97/5.18  thf('323', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('324', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('325', plain,
% 4.97/5.18      ((((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['322', '323', '324'])).
% 4.97/5.18  thf('326', plain,
% 4.97/5.18      ((((sk_B) != (k2_relat_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup-', [status(thm)], ['244', '325'])).
% 4.97/5.18  thf('327', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.18      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.18  thf('328', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('329', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('330', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('331', plain,
% 4.97/5.18      ((((sk_B) != (sk_B)) | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['326', '327', '328', '329', '330'])).
% 4.97/5.18  thf('332', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('simplify', [status(thm)], ['331'])).
% 4.97/5.18  thf('333', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18             (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['243', '332'])).
% 4.97/5.18  thf('334', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.18  thf('335', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 4.97/5.18            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 4.97/5.18          | ~ (v1_relat_1 @ X1)
% 4.97/5.18          | ~ (v1_funct_1 @ X1)
% 4.97/5.18          | ~ (v2_funct_1 @ X1))),
% 4.97/5.18      inference('demod', [status(thm)], ['40', '43', '46', '49'])).
% 4.97/5.18  thf('336', plain,
% 4.97/5.18      (![X10 : $i]:
% 4.97/5.18         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.97/5.18          | ~ (v1_funct_1 @ X10)
% 4.97/5.18          | ~ (v1_relat_1 @ X10))),
% 4.97/5.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.97/5.18  thf('337', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         ((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ (k2_funct_1 @ X0)))
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 4.97/5.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1))))),
% 4.97/5.18      inference('sup+', [status(thm)], ['335', '336'])).
% 4.97/5.18  thf('338', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | (v1_funct_1 @ 
% 4.97/5.18           (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['334', '337'])).
% 4.97/5.18  thf('339', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('340', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.18  thf('341', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('342', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('343', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('344', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('345', plain,
% 4.97/5.18      ((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['338', '339', '340', '341', '342', '343', '344'])).
% 4.97/5.18  thf('346', plain,
% 4.97/5.18      (((k2_funct_1 @ sk_C)
% 4.97/5.18         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 4.97/5.18  thf('347', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['345', '346'])).
% 4.97/5.18  thf('348', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18             (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['333', '347'])).
% 4.97/5.18  thf('349', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['240', '348'])).
% 4.97/5.18  thf('350', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('351', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('352', plain,
% 4.97/5.18      (((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18         = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18            (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)], ['349', '350', '351'])).
% 4.97/5.18  thf('353', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 4.97/5.18              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['3', '4'])).
% 4.97/5.18  thf('354', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('simplify', [status(thm)], ['331'])).
% 4.97/5.18  thf('355', plain,
% 4.97/5.18      (![X20 : $i]:
% 4.97/5.18         (~ (v2_funct_1 @ X20)
% 4.97/5.18          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 4.97/5.18          | ~ (v1_funct_1 @ X20)
% 4.97/5.18          | ~ (v1_relat_1 @ X20))),
% 4.97/5.18      inference('demod', [status(thm)], ['0', '1'])).
% 4.97/5.18  thf('356', plain,
% 4.97/5.18      (![X21 : $i, X22 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X21)
% 4.97/5.18          | ~ (v1_funct_1 @ X21)
% 4.97/5.18          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 4.97/5.18              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 4.97/5.18          | ~ (v2_funct_1 @ X21)
% 4.97/5.18          | ~ (v2_funct_1 @ X22)
% 4.97/5.18          | ~ (v1_funct_1 @ X22)
% 4.97/5.18          | ~ (v1_relat_1 @ X22))),
% 4.97/5.18      inference('cnf', [status(esa)], [t66_funct_1])).
% 4.97/5.18  thf('357', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (((k2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 4.97/5.18            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 4.97/5.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0))),
% 4.97/5.18      inference('sup+', [status(thm)], ['355', '356'])).
% 4.97/5.18  thf('358', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.97/5.18          | ((k2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 4.97/5.18              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 4.97/5.18      inference('simplify', [status(thm)], ['357'])).
% 4.97/5.18  thf('359', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 4.97/5.18          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C))),
% 4.97/5.18      inference('sup-', [status(thm)], ['354', '358'])).
% 4.97/5.18  thf('360', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.18  thf('361', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['345', '346'])).
% 4.97/5.18  thf('362', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('363', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('364', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('365', plain,
% 4.97/5.18      (((k2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 4.97/5.18         = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['359', '360', '361', '362', '363', '364'])).
% 4.97/5.18  thf('366', plain,
% 4.97/5.18      ((((k2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 4.97/5.18          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C))),
% 4.97/5.18      inference('sup+', [status(thm)], ['353', '365'])).
% 4.97/5.18  thf('367', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.97/5.18      inference('sup+', [status(thm)], ['26', '27'])).
% 4.97/5.18  thf('368', plain,
% 4.97/5.18      (![X23 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X23)) = (k6_partfun1 @ X23))),
% 4.97/5.18      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.97/5.18  thf('369', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('370', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('371', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('372', plain,
% 4.97/5.18      (((k6_partfun1 @ sk_B)
% 4.97/5.18         = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['366', '367', '368', '369', '370', '371'])).
% 4.97/5.18  thf('373', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 4.97/5.18      inference('demod', [status(thm)], ['279', '280'])).
% 4.97/5.18  thf('374', plain,
% 4.97/5.18      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 4.97/5.18         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup+', [status(thm)], ['372', '373'])).
% 4.97/5.18  thf('375', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 4.97/5.18      inference('demod', [status(thm)], ['279', '280'])).
% 4.97/5.18  thf('376', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['374', '375'])).
% 4.97/5.18  thf('377', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['32', '33'])).
% 4.97/5.18  thf('378', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.18  thf('379', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['345', '346'])).
% 4.97/5.18  thf('380', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('simplify', [status(thm)], ['331'])).
% 4.97/5.18  thf('381', plain,
% 4.97/5.18      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 4.97/5.18         = (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 4.97/5.18  thf('382', plain,
% 4.97/5.18      (![X0 : $i, X1 : $i]:
% 4.97/5.18         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ (k2_funct_1 @ X0)))
% 4.97/5.18          | ~ (v2_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_funct_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ X0)
% 4.97/5.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 4.97/5.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1))))),
% 4.97/5.18      inference('sup+', [status(thm)], ['50', '51'])).
% 4.97/5.18  thf('383', plain,
% 4.97/5.18      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ 
% 4.97/5.18             (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | (v1_relat_1 @ 
% 4.97/5.18           (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18            (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 4.97/5.18      inference('sup-', [status(thm)], ['381', '382'])).
% 4.97/5.18  thf('384', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['345', '346'])).
% 4.97/5.18  thf('385', plain,
% 4.97/5.18      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 4.97/5.18         = (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 4.97/5.18  thf('386', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['345', '346'])).
% 4.97/5.18  thf('387', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('simplify', [status(thm)], ['331'])).
% 4.97/5.18  thf('388', plain,
% 4.97/5.18      (((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18         = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 4.97/5.18            (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)], ['349', '350', '351'])).
% 4.97/5.18  thf('389', plain,
% 4.97/5.18      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.97/5.18        | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['383', '384', '385', '386', '387', '388'])).
% 4.97/5.18  thf('390', plain,
% 4.97/5.18      (((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('simplify', [status(thm)], ['389'])).
% 4.97/5.18  thf('391', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.18  thf('392', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['390', '391'])).
% 4.97/5.18  thf('393', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['239', '352', '376', '377', '378', '379', '380', '392'])).
% 4.97/5.18  thf('394', plain, ((v1_relat_1 @ sk_D)),
% 4.97/5.18      inference('demod', [status(thm)], ['96', '97'])).
% 4.97/5.18  thf('395', plain, ((v1_funct_1 @ sk_D)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('396', plain, ((v2_funct_1 @ sk_D)),
% 4.97/5.18      inference('simplify', [status(thm)], ['173'])).
% 4.97/5.18  thf('397', plain,
% 4.97/5.18      (((sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ sk_B)))),
% 4.97/5.18      inference('demod', [status(thm)], ['236', '393', '394', '395', '396'])).
% 4.97/5.18  thf('398', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 4.97/5.18      inference('sup+', [status(thm)], ['188', '397'])).
% 4.97/5.18  thf('399', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 4.97/5.18      inference('demod', [status(thm)], ['175', '398'])).
% 4.97/5.18  thf('400', plain,
% 4.97/5.18      (![X0 : $i]:
% 4.97/5.18         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 4.97/5.18            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ X0)))
% 4.97/5.18          | ~ (v1_relat_1 @ X0))),
% 4.97/5.18      inference('demod', [status(thm)], ['112', '399'])).
% 4.97/5.18  thf('401', plain,
% 4.97/5.18      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 4.97/5.18          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 4.97/5.18        | ~ (v1_relat_1 @ sk_C)
% 4.97/5.18        | ~ (v1_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v2_funct_1 @ sk_C)
% 4.97/5.18        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('sup+', [status(thm)], ['2', '400'])).
% 4.97/5.18  thf('402', plain,
% 4.97/5.18      (((k2_funct_1 @ sk_C)
% 4.97/5.18         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))),
% 4.97/5.18      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 4.97/5.18  thf('403', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)], ['209', '216', '219'])).
% 4.97/5.18  thf('404', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 4.97/5.18      inference('demod', [status(thm)], ['93', '98'])).
% 4.97/5.18  thf('405', plain, ((v1_relat_1 @ sk_C)),
% 4.97/5.18      inference('demod', [status(thm)], ['21', '22'])).
% 4.97/5.18  thf('406', plain, ((v1_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('407', plain, ((v2_funct_1 @ sk_C)),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('408', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['53', '54', '55', '56', '57', '58', '59', '66'])).
% 4.97/5.18  thf('409', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 4.97/5.18      inference('demod', [status(thm)],
% 4.97/5.18                ['401', '402', '403', '404', '405', '406', '407', '408'])).
% 4.97/5.18  thf('410', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 4.97/5.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.97/5.18  thf('411', plain, ($false),
% 4.97/5.18      inference('simplify_reflect-', [status(thm)], ['409', '410'])).
% 4.97/5.18  
% 4.97/5.18  % SZS output end Refutation
% 4.97/5.18  
% 5.01/5.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
