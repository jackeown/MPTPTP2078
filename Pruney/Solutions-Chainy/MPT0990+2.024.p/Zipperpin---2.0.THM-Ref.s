%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rFuCD9LeTn

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:57 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 390 expanded)
%              Number of leaves         :   42 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          : 1449 (6981 expanded)
%              Number of equality atoms :   78 ( 479 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('46',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('47',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75'])).

thf('77',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','76'])).

thf('78',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('84',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('91',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','94','95','96','97'])).

thf('99',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['49','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','103'])).

thf('105',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['100','101'])).

thf('117',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['100','101'])).

thf('119',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','117','118'])).

thf('120',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rFuCD9LeTn
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:09:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.02/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.20  % Solved by: fo/fo7.sh
% 1.02/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.20  % done 705 iterations in 0.749s
% 1.02/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.20  % SZS output start Refutation
% 1.02/1.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.02/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.02/1.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.02/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.02/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.02/1.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.02/1.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.02/1.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.02/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.02/1.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.02/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.02/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.02/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.02/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.02/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.02/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.02/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.02/1.20  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.02/1.20  thf(t94_relat_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( v1_relat_1 @ B ) =>
% 1.02/1.20       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.02/1.20  thf('0', plain,
% 1.02/1.20      (![X5 : $i, X6 : $i]:
% 1.02/1.20         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_relat_1 @ X5) @ X6))
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.02/1.20  thf(redefinition_k6_partfun1, axiom,
% 1.02/1.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.02/1.20  thf('1', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('2', plain,
% 1.02/1.20      (![X5 : $i, X6 : $i]:
% 1.02/1.20         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.02/1.20  thf('3', plain,
% 1.02/1.20      (![X5 : $i, X6 : $i]:
% 1.02/1.20         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.02/1.20  thf(t67_funct_1, axiom,
% 1.02/1.20    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.02/1.20  thf('4', plain,
% 1.02/1.20      (![X15 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X15)) = (k6_relat_1 @ X15))),
% 1.02/1.20      inference('cnf', [status(esa)], [t67_funct_1])).
% 1.02/1.20  thf('5', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('6', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('7', plain,
% 1.02/1.20      (![X15 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X15)) = (k6_partfun1 @ X15))),
% 1.02/1.20      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.02/1.20  thf(t66_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ![B:$i]:
% 1.02/1.20         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.02/1.20           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 1.02/1.20             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.02/1.20               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 1.02/1.20  thf('8', plain,
% 1.02/1.20      (![X13 : $i, X14 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X13)
% 1.02/1.20          | ~ (v1_funct_1 @ X13)
% 1.02/1.20          | ((k2_funct_1 @ (k5_relat_1 @ X14 @ X13))
% 1.02/1.20              = (k5_relat_1 @ (k2_funct_1 @ X13) @ (k2_funct_1 @ X14)))
% 1.02/1.20          | ~ (v2_funct_1 @ X13)
% 1.02/1.20          | ~ (v2_funct_1 @ X14)
% 1.02/1.20          | ~ (v1_funct_1 @ X14)
% 1.02/1.20          | ~ (v1_relat_1 @ X14))),
% 1.02/1.20      inference('cnf', [status(esa)], [t66_funct_1])).
% 1.02/1.20  thf('9', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['7', '8'])).
% 1.02/1.20  thf(fc3_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.02/1.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.02/1.20  thf('10', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.02/1.20  thf('11', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('12', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 1.02/1.20      inference('demod', [status(thm)], ['10', '11'])).
% 1.02/1.20  thf('13', plain, (![X9 : $i]: (v1_funct_1 @ (k6_relat_1 @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.02/1.20  thf('14', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('15', plain, (![X9 : $i]: (v1_funct_1 @ (k6_partfun1 @ X9))),
% 1.02/1.20      inference('demod', [status(thm)], ['13', '14'])).
% 1.02/1.20  thf(fc4_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.02/1.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.02/1.20  thf('16', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.02/1.20  thf('17', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('18', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 1.02/1.20      inference('demod', [status(thm)], ['16', '17'])).
% 1.02/1.20  thf('19', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 1.02/1.20  thf('20', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v2_funct_1 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['3', '19'])).
% 1.02/1.20  thf('21', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20              = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.02/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.20  thf(t36_funct_2, conjecture,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ![D:$i]:
% 1.02/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.02/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.02/1.20           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.02/1.20               ( r2_relset_1 @
% 1.02/1.20                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.02/1.20                 ( k6_partfun1 @ A ) ) & 
% 1.02/1.20               ( v2_funct_1 @ C ) ) =>
% 1.02/1.20             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.02/1.20               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.02/1.20        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20          ( ![D:$i]:
% 1.02/1.20            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.02/1.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.02/1.20              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.02/1.20                  ( r2_relset_1 @
% 1.02/1.20                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.02/1.20                    ( k6_partfun1 @ A ) ) & 
% 1.02/1.20                  ( v2_funct_1 @ C ) ) =>
% 1.02/1.20                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.02/1.20                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.02/1.20    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.02/1.20  thf('22', plain,
% 1.02/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.02/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.02/1.20        (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('23', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('24', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(redefinition_k1_partfun1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.02/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( v1_funct_1 @ F ) & 
% 1.02/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.02/1.20       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.02/1.20  thf('25', plain,
% 1.02/1.20      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.02/1.20          | ~ (v1_funct_1 @ X36)
% 1.02/1.20          | ~ (v1_funct_1 @ X39)
% 1.02/1.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.02/1.20          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 1.02/1.20              = (k5_relat_1 @ X36 @ X39)))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.02/1.20  thf('26', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['24', '25'])).
% 1.02/1.20  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('28', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.02/1.20          | ~ (v1_funct_1 @ X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['26', '27'])).
% 1.02/1.20  thf('29', plain,
% 1.02/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['23', '28'])).
% 1.02/1.20  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('31', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['29', '30'])).
% 1.02/1.20  thf('32', plain,
% 1.02/1.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20        (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['22', '31'])).
% 1.02/1.20  thf('33', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('34', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(dt_k1_partfun1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.02/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( v1_funct_1 @ F ) & 
% 1.02/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.02/1.20       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.02/1.20         ( m1_subset_1 @
% 1.02/1.20           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.02/1.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.02/1.20  thf('35', plain,
% 1.02/1.20      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.02/1.20          | ~ (v1_funct_1 @ X30)
% 1.02/1.20          | ~ (v1_funct_1 @ X33)
% 1.02/1.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.02/1.20          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 1.02/1.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.02/1.20  thf('36', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.02/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['34', '35'])).
% 1.02/1.20  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('38', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.02/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['36', '37'])).
% 1.02/1.20  thf('39', plain,
% 1.02/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | (m1_subset_1 @ 
% 1.02/1.20           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['33', '38'])).
% 1.02/1.20  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('41', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['29', '30'])).
% 1.02/1.20  thf('42', plain,
% 1.02/1.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.02/1.20  thf(redefinition_r2_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.02/1.20  thf('43', plain,
% 1.02/1.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.02/1.20          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.02/1.20          | ((X25) = (X28))
% 1.02/1.20          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.02/1.20  thf('44', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.02/1.20          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['42', '43'])).
% 1.02/1.20  thf('45', plain,
% 1.02/1.20      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.02/1.20        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['32', '44'])).
% 1.02/1.20  thf(t29_relset_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( m1_subset_1 @
% 1.02/1.20       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.02/1.20  thf('46', plain,
% 1.02/1.20      (![X29 : $i]:
% 1.02/1.20         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.02/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.02/1.20  thf('47', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('48', plain,
% 1.02/1.20      (![X29 : $i]:
% 1.02/1.20         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.02/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.02/1.20      inference('demod', [status(thm)], ['46', '47'])).
% 1.02/1.20  thf('49', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['45', '48'])).
% 1.02/1.20  thf('50', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20              = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.02/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.20  thf('51', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(cc2_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.02/1.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.02/1.20  thf('52', plain,
% 1.02/1.20      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.20         ((v4_relat_1 @ X19 @ X20)
% 1.02/1.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.02/1.20  thf('53', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.02/1.20      inference('sup-', [status(thm)], ['51', '52'])).
% 1.02/1.20  thf(t209_relat_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.02/1.20       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.02/1.20  thf('54', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.02/1.20          | ~ (v4_relat_1 @ X0 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.02/1.20  thf('55', plain,
% 1.02/1.20      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['53', '54'])).
% 1.02/1.20  thf('56', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(cc1_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.02/1.20       ( v1_relat_1 @ C ) ))).
% 1.02/1.20  thf('57', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.02/1.20         ((v1_relat_1 @ X16)
% 1.02/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.02/1.20  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('59', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '58'])).
% 1.02/1.20  thf('60', plain,
% 1.02/1.20      (![X5 : $i, X6 : $i]:
% 1.02/1.20         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.02/1.20  thf('61', plain,
% 1.02/1.20      (![X5 : $i, X6 : $i]:
% 1.02/1.20         (((k7_relat_1 @ X6 @ X5) = (k5_relat_1 @ (k6_partfun1 @ X5) @ X6))
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('demod', [status(thm)], ['0', '1'])).
% 1.02/1.20  thf('62', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 1.02/1.20  thf(dt_k2_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.02/1.20         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.02/1.20  thf('63', plain,
% 1.02/1.20      (![X7 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.02/1.20          | ~ (v1_funct_1 @ X7)
% 1.02/1.20          | ~ (v1_relat_1 @ X7))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf('64', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))),
% 1.02/1.20      inference('sup+', [status(thm)], ['62', '63'])).
% 1.02/1.20  thf('65', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['61', '64'])).
% 1.02/1.20  thf('66', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['65'])).
% 1.02/1.20  thf('67', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['60', '66'])).
% 1.02/1.20  thf('68', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v2_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['67'])).
% 1.02/1.20  thf('69', plain,
% 1.02/1.20      ((~ (v1_funct_1 @ sk_C)
% 1.02/1.20        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_C)
% 1.02/1.20        | ~ (v2_funct_1 @ sk_C)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.02/1.20        | (v1_relat_1 @ 
% 1.02/1.20           (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['59', '68'])).
% 1.02/1.20  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('71', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '58'])).
% 1.02/1.20  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('76', plain,
% 1.02/1.20      ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)],
% 1.02/1.20                ['69', '70', '71', '72', '73', '74', '75'])).
% 1.02/1.20  thf('77', plain,
% 1.02/1.20      (((v1_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_C)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.02/1.20        | ~ (v2_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup+', [status(thm)], ['50', '76'])).
% 1.02/1.20  thf('78', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '58'])).
% 1.02/1.20  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('82', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.02/1.20      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 1.02/1.20  thf(t61_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v2_funct_1 @ A ) =>
% 1.02/1.20         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.02/1.20             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.02/1.20           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.02/1.20             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.02/1.20  thf('83', plain,
% 1.02/1.20      (![X12 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X12)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.02/1.20              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 1.02/1.20          | ~ (v1_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_relat_1 @ X12))),
% 1.02/1.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.02/1.20  thf('84', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('85', plain,
% 1.02/1.20      (![X12 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X12)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.02/1.20              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.02/1.20          | ~ (v1_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_relat_1 @ X12))),
% 1.02/1.20      inference('demod', [status(thm)], ['83', '84'])).
% 1.02/1.20  thf(t55_relat_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( v1_relat_1 @ A ) =>
% 1.02/1.20       ( ![B:$i]:
% 1.02/1.20         ( ( v1_relat_1 @ B ) =>
% 1.02/1.20           ( ![C:$i]:
% 1.02/1.20             ( ( v1_relat_1 @ C ) =>
% 1.02/1.20               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.02/1.20                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.02/1.20  thf('86', plain,
% 1.02/1.20      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X2)
% 1.02/1.20          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.02/1.20              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.02/1.20          | ~ (v1_relat_1 @ X4)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.02/1.20  thf('87', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('sup+', [status(thm)], ['85', '86'])).
% 1.02/1.20  thf('88', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.02/1.20              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.02/1.20      inference('simplify', [status(thm)], ['87'])).
% 1.02/1.20  thf('89', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ X0)
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ sk_C)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C)
% 1.02/1.20          | ~ (v2_funct_1 @ sk_C)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['82', '88'])).
% 1.02/1.20  thf('90', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(redefinition_k2_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.02/1.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.02/1.20  thf('91', plain,
% 1.02/1.20      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.20         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.02/1.20          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.02/1.20  thf('92', plain,
% 1.02/1.20      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['90', '91'])).
% 1.02/1.20  thf('93', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.02/1.20      inference('sup+', [status(thm)], ['92', '93'])).
% 1.02/1.20  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('98', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.02/1.20            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['89', '94', '95', '96', '97'])).
% 1.02/1.20  thf('99', plain,
% 1.02/1.20      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.02/1.20          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_D))),
% 1.02/1.20      inference('sup+', [status(thm)], ['49', '98'])).
% 1.02/1.20  thf('100', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('101', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.02/1.20         ((v1_relat_1 @ X16)
% 1.02/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.02/1.20  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['100', '101'])).
% 1.02/1.20  thf('103', plain,
% 1.02/1.20      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)], ['99', '102'])).
% 1.02/1.20  thf('104', plain,
% 1.02/1.20      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.02/1.20          = (k2_funct_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_C)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.02/1.20        | ~ (v2_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup+', [status(thm)], ['21', '103'])).
% 1.02/1.20  thf('105', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '58'])).
% 1.02/1.20  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.20  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('109', plain,
% 1.02/1.20      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.02/1.20      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 1.02/1.20  thf('110', plain,
% 1.02/1.20      ((((k7_relat_1 @ sk_D @ sk_B) = (k2_funct_1 @ sk_C))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_D))),
% 1.02/1.20      inference('sup+', [status(thm)], ['2', '109'])).
% 1.02/1.20  thf('111', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('112', plain,
% 1.02/1.20      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.20         ((v4_relat_1 @ X19 @ X20)
% 1.02/1.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.02/1.20  thf('113', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.02/1.20      inference('sup-', [status(thm)], ['111', '112'])).
% 1.02/1.20  thf('114', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.02/1.20          | ~ (v4_relat_1 @ X0 @ X1)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.02/1.20  thf('115', plain,
% 1.02/1.20      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['113', '114'])).
% 1.02/1.20  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['100', '101'])).
% 1.02/1.20  thf('117', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.02/1.20      inference('demod', [status(thm)], ['115', '116'])).
% 1.02/1.20  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['100', '101'])).
% 1.02/1.20  thf('119', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.02/1.20      inference('demod', [status(thm)], ['110', '117', '118'])).
% 1.02/1.20  thf('120', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('121', plain, ($false),
% 1.02/1.20      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 1.02/1.20  
% 1.02/1.20  % SZS output end Refutation
% 1.02/1.20  
% 1.05/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
