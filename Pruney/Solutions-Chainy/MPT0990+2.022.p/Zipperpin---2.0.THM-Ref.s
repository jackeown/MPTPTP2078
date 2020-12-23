%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oK3tjnDTvM

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:57 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 388 expanded)
%              Number of leaves         :   43 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          : 1441 (6968 expanded)
%              Number of equality atoms :   77 ( 477 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X15 ) )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('5',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X15 ) )
      = ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('17',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

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

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('42',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('46',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('47',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','15','18'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73'])).

thf('75',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','74'])).

thf('76',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('82',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','92','93','94','95'])).

thf('97',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['47','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','101'])).

thf('103',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('115',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('117',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','115','116'])).

thf('118',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oK3tjnDTvM
% 0.09/0.30  % Computer   : n003.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 17:23:57 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  % Running portfolio for 600 s
% 0.09/0.30  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.31  % Number of cores: 8
% 0.16/0.31  % Python version: Python 3.6.8
% 0.16/0.31  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 845 iterations in 0.845s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.05/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.24  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.05/1.24  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.05/1.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.05/1.24  thf(t94_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_relat_1 @ X5) @ X6))
% 1.05/1.24          | ~ (v1_relat_1 @ X6))),
% 1.05/1.24      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.05/1.24  thf(redefinition_k6_partfun1, axiom,
% 1.05/1.24    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.05/1.24  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('2', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.05/1.24          | ~ (v1_relat_1 @ X6))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.24  thf('3', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.05/1.24          | ~ (v1_relat_1 @ X6))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.24  thf(t67_funct_1, axiom,
% 1.05/1.24    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.05/1.24  thf('4', plain,
% 1.05/1.24      (![X15 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X15)) = (k6_relat_1 @ X15))),
% 1.05/1.24      inference('cnf', [status(esa)], [t67_funct_1])).
% 1.05/1.24  thf('5', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('6', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('7', plain,
% 1.05/1.24      (![X15 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X15)) = (k6_partfun1 @ X15))),
% 1.05/1.24      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.05/1.24  thf(t66_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ![B:$i]:
% 1.05/1.24         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.24           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 1.05/1.24             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.05/1.24               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 1.05/1.24  thf('8', plain,
% 1.05/1.24      (![X13 : $i, X14 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X13)
% 1.05/1.24          | ~ (v1_funct_1 @ X13)
% 1.05/1.24          | ((k2_funct_1 @ (k5_relat_1 @ X14 @ X13))
% 1.05/1.24              = (k5_relat_1 @ (k2_funct_1 @ X13) @ (k2_funct_1 @ X14)))
% 1.05/1.24          | ~ (v2_funct_1 @ X13)
% 1.05/1.24          | ~ (v2_funct_1 @ X14)
% 1.05/1.24          | ~ (v1_funct_1 @ X14)
% 1.05/1.24          | ~ (v1_relat_1 @ X14))),
% 1.05/1.24      inference('cnf', [status(esa)], [t66_funct_1])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.05/1.24          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.05/1.24          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1))),
% 1.05/1.24      inference('sup+', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf(fc3_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.05/1.24       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.05/1.24  thf('10', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.05/1.24  thf('11', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('12', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 1.05/1.24      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.24  thf('13', plain, (![X9 : $i]: (v1_funct_1 @ (k6_relat_1 @ X9))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.05/1.24  thf('14', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('15', plain, (![X9 : $i]: (v1_funct_1 @ (k6_partfun1 @ X9))),
% 1.05/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.05/1.24  thf(fc4_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.05/1.24       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.05/1.24  thf('16', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.05/1.24  thf('17', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('18', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 1.05/1.24      inference('demod', [status(thm)], ['16', '17'])).
% 1.05/1.24  thf('19', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 1.05/1.24  thf('20', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v2_funct_1 @ X1))),
% 1.05/1.24      inference('sup+', [status(thm)], ['3', '19'])).
% 1.05/1.24  thf('21', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24              = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.05/1.24      inference('simplify', [status(thm)], ['20'])).
% 1.05/1.24  thf(t36_funct_2, conjecture,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24       ( ![D:$i]:
% 1.05/1.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.24           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.24               ( r2_relset_1 @
% 1.05/1.24                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.24                 ( k6_partfun1 @ A ) ) & 
% 1.05/1.24               ( v2_funct_1 @ C ) ) =>
% 1.05/1.24             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.24        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.24            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24          ( ![D:$i]:
% 1.05/1.24            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.24                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.24              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.24                  ( r2_relset_1 @
% 1.05/1.24                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.24                    ( k6_partfun1 @ A ) ) & 
% 1.05/1.24                  ( v2_funct_1 @ C ) ) =>
% 1.05/1.24                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.05/1.24  thf('22', plain,
% 1.05/1.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.24        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.24        (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('23', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('24', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.05/1.24  thf('25', plain,
% 1.05/1.24      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.05/1.24          | ~ (v1_funct_1 @ X37)
% 1.05/1.24          | ~ (v1_funct_1 @ X40)
% 1.05/1.24          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.05/1.24          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 1.05/1.24              = (k5_relat_1 @ X37 @ X40)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.24  thf('26', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['24', '25'])).
% 1.05/1.24  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['26', '27'])).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.24        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['23', '28'])).
% 1.05/1.24  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.24      inference('demod', [status(thm)], ['29', '30'])).
% 1.05/1.24  thf('32', plain,
% 1.05/1.24      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.24        (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['22', '31'])).
% 1.05/1.24  thf('33', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('34', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(dt_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.05/1.24         ( m1_subset_1 @
% 1.05/1.24           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.05/1.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.05/1.24  thf('35', plain,
% 1.05/1.24      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.05/1.24          | ~ (v1_funct_1 @ X29)
% 1.05/1.24          | ~ (v1_funct_1 @ X32)
% 1.05/1.24          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.05/1.24          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 1.05/1.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.05/1.24  thf('36', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('38', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.24  thf('39', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.24        | (m1_subset_1 @ 
% 1.05/1.24           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['33', '38'])).
% 1.05/1.24  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('41', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.24      inference('demod', [status(thm)], ['29', '30'])).
% 1.05/1.24  thf('42', plain,
% 1.05/1.24      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.05/1.24      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.05/1.24  thf(redefinition_r2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.05/1.24  thf('43', plain,
% 1.05/1.24      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.05/1.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.05/1.24          | ((X25) = (X28))
% 1.05/1.24          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.05/1.24  thf('44', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.05/1.24          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['42', '43'])).
% 1.05/1.24  thf('45', plain,
% 1.05/1.24      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.05/1.24        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['32', '44'])).
% 1.05/1.24  thf(dt_k6_partfun1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( m1_subset_1 @
% 1.05/1.24         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.05/1.24       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.05/1.24  thf('46', plain,
% 1.05/1.24      (![X36 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.05/1.24  thf('47', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['45', '46'])).
% 1.05/1.24  thf('48', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24              = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.05/1.24      inference('simplify', [status(thm)], ['20'])).
% 1.05/1.24  thf('49', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.24  thf('50', plain,
% 1.05/1.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X19 @ X20)
% 1.05/1.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('51', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf(t209_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.05/1.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.05/1.24  thf('52', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.05/1.24          | ~ (v4_relat_1 @ X0 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.05/1.24  thf('53', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['51', '52'])).
% 1.05/1.24  thf('54', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc1_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( v1_relat_1 @ C ) ))).
% 1.05/1.24  thf('55', plain,
% 1.05/1.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ X16)
% 1.05/1.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.24  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('57', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['53', '56'])).
% 1.05/1.24  thf('58', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.05/1.24          | ~ (v1_relat_1 @ X6))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.24  thf('59', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.05/1.24          | ~ (v1_relat_1 @ X6))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.24  thf('60', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 1.05/1.24  thf(dt_k2_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.05/1.24         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.05/1.24  thf('61', plain,
% 1.05/1.24      (![X7 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.05/1.24          | ~ (v1_funct_1 @ X7)
% 1.05/1.24          | ~ (v1_relat_1 @ X7))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf('62', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['60', '61'])).
% 1.05/1.24  thf('63', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['59', '62'])).
% 1.05/1.24  thf('64', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.05/1.24      inference('simplify', [status(thm)], ['63'])).
% 1.05/1.24  thf('65', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['58', '64'])).
% 1.05/1.24  thf('66', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v2_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.05/1.24      inference('simplify', [status(thm)], ['65'])).
% 1.05/1.24  thf('67', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | (v1_relat_1 @ 
% 1.05/1.24           (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['57', '66'])).
% 1.05/1.24  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['53', '56'])).
% 1.05/1.24  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('74', plain,
% 1.05/1.24      ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.05/1.24      inference('demod', [status(thm)],
% 1.05/1.24                ['67', '68', '69', '70', '71', '72', '73'])).
% 1.05/1.24  thf('75', plain,
% 1.05/1.24      (((v1_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['48', '74'])).
% 1.05/1.24  thf('76', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['53', '56'])).
% 1.05/1.24  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('80', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 1.05/1.24  thf(t61_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v2_funct_1 @ A ) =>
% 1.05/1.24         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.05/1.24             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.05/1.24           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.05/1.24             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.05/1.24  thf('81', plain,
% 1.05/1.24      (![X12 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X12)
% 1.05/1.24          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.05/1.24              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 1.05/1.24          | ~ (v1_funct_1 @ X12)
% 1.05/1.24          | ~ (v1_relat_1 @ X12))),
% 1.05/1.24      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.05/1.24  thf('82', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('83', plain,
% 1.05/1.24      (![X12 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X12)
% 1.05/1.24          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.05/1.24              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.05/1.24          | ~ (v1_funct_1 @ X12)
% 1.05/1.24          | ~ (v1_relat_1 @ X12))),
% 1.05/1.24      inference('demod', [status(thm)], ['81', '82'])).
% 1.05/1.24  thf(t55_relat_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ A ) =>
% 1.05/1.24       ( ![B:$i]:
% 1.05/1.24         ( ( v1_relat_1 @ B ) =>
% 1.05/1.24           ( ![C:$i]:
% 1.05/1.24             ( ( v1_relat_1 @ C ) =>
% 1.05/1.24               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.05/1.24                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.05/1.24  thf('84', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X2)
% 1.05/1.24          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.05/1.24              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.05/1.24          | ~ (v1_relat_1 @ X4)
% 1.05/1.24          | ~ (v1_relat_1 @ X3))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.05/1.24  thf('85', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['83', '84'])).
% 1.05/1.24  thf('86', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.05/1.24              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.05/1.24      inference('simplify', [status(thm)], ['85'])).
% 1.05/1.24  thf('87', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24          | ~ (v2_funct_1 @ sk_C)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['80', '86'])).
% 1.05/1.24  thf('88', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.24  thf('89', plain,
% 1.05/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.24         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.05/1.24          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.24  thf('90', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['88', '89'])).
% 1.05/1.24  thf('91', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['90', '91'])).
% 1.05/1.24  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('96', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['87', '92', '93', '94', '95'])).
% 1.05/1.24  thf('97', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.05/1.24          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup+', [status(thm)], ['47', '96'])).
% 1.05/1.24  thf('98', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('99', plain,
% 1.05/1.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ X16)
% 1.05/1.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.24  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.24  thf('101', plain,
% 1.05/1.24      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.05/1.24         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.05/1.24      inference('demod', [status(thm)], ['97', '100'])).
% 1.05/1.24  thf('102', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.05/1.24          = (k2_funct_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['21', '101'])).
% 1.05/1.24  thf('103', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['53', '56'])).
% 1.05/1.24  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('107', plain,
% 1.05/1.24      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 1.05/1.24  thf('108', plain,
% 1.05/1.24      ((((k7_relat_1 @ sk_D @ sk_B) = (k2_funct_1 @ sk_C))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup+', [status(thm)], ['2', '107'])).
% 1.05/1.24  thf('109', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('110', plain,
% 1.05/1.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X19 @ X20)
% 1.05/1.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('111', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.05/1.24      inference('sup-', [status(thm)], ['109', '110'])).
% 1.05/1.24  thf('112', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.05/1.24          | ~ (v4_relat_1 @ X0 @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.05/1.24  thf('113', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['111', '112'])).
% 1.05/1.24  thf('114', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.24  thf('115', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.05/1.24      inference('demod', [status(thm)], ['113', '114'])).
% 1.05/1.24  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.24  thf('117', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['108', '115', '116'])).
% 1.05/1.24  thf('118', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('119', plain, ($false),
% 1.05/1.24      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
