%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tiRijv32YV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:58 EST 2020

% Result     : Theorem 29.04s
% Output     : Refutation 29.04s
% Verified   : 
% Statistics : Number of formulae       :  395 (39319 expanded)
%              Number of leaves         :   50 (11936 expanded)
%              Depth                    :   75
%              Number of atoms          : 3677 (801454 expanded)
%              Number of equality atoms :  255 (52095 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','12','27'])).

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

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

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

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k2_funct_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X13 ) )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('36',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X13 ) )
      = ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('41',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('45',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('51',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('52',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('66',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('79',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('81',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('82',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('86',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X13 ) )
      = ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['78','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('105',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('107',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','105','108','109','110'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X13 ) )
      = ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('113',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('116',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('117',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('118',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115','118'])).

thf('120',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','105','108','109','110'])).

thf('122',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X13 ) )
      = ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('123',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('126',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('130',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('131',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      = ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('133',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('135',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','135','136','137','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('141',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','140'])).

thf('142',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','141'])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('149',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ( ( k6_partfun1 @ sk_A )
      = ( k2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('151',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('152',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','105','108','109','110'])).

thf('153',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('154',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','135','136','137','138'])).

thf('156',plain,(
    ! [X13: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X13 ) )
      = ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('157',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('158',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('159',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
     != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ) )
    | ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k6_partfun1 @ sk_A )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156','157','158'])).

thf('160',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('162',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ X0 )
      | ( ( k6_partfun1 @ sk_A )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      | ( ( k6_partfun1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['63','164'])).

thf('166',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      | ( ( k6_partfun1 @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['165','166','167','168','169'])).

thf('171',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','170'])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('175',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ~ ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','175'])).

thf('177',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('178',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('180',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('187',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    r2_relset_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) ),
    inference('sup-',[status(thm)],['185','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','188','189','190','191'])).

thf('193',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('194',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('197',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('198',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('203',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195','200','201','202'])).

thf('204',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('208',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','188','189','190','191'])).

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

thf('209',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('210',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('212',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211','212','213','214'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['207','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('222',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','223'])).

thf('225',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226','227','228'])).

thf('230',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','230'])).

thf('232',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','231'])).

thf('233',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','239'])).

thf('241',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244'])).

thf('246',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('248',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74','77'])).

thf('250',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('251',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['248','249','250'])).

thf('252',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['40','251'])).

thf('253',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('254',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('263',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('264',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('265',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('267',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('268',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['262','268'])).

thf('270',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('271',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['261','272'])).

thf('274',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['273','274','275'])).

thf('277',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('278',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('280',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('285',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','38','259','260','276','277','280','281','282','283','284'])).

thf('286',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','12','27'])).

thf('288',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('289',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('291',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('292',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['198','199'])).

thf('294',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('296',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('298',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('300',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['297','300'])).

thf('302',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['301','302'])).

thf('304',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('306',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['296','303','306'])).

thf('308',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('310',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['289','290','291','292','293','307','308','309'])).

thf('311',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['310'])).

thf('312',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['286','311'])).

thf('313',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','312'])).

thf('314',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','316'])).

thf('318',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('319',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['317','318','319'])).

thf('321',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['2','320'])).

thf('322',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('323',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['321','322','323'])).

thf('325',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','324'])).

thf('326',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('327',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('329',plain,
    ( ( ( k1_relat_1 @ sk_D )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','328'])).

thf('330',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['296','303','306'])).

thf('331',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('332',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['310'])).

thf('334',plain,
    ( ( sk_B != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference(demod,[status(thm)],['329','330','331','332','333'])).

thf('335',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('337',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['335','336'])).

thf('338',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['278','279'])).

thf('339',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['310'])).

thf('341',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['341','342'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tiRijv32YV
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.04/29.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.04/29.28  % Solved by: fo/fo7.sh
% 29.04/29.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.04/29.28  % done 6083 iterations in 28.815s
% 29.04/29.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.04/29.28  % SZS output start Refutation
% 29.04/29.28  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 29.04/29.28  thf(sk_A_type, type, sk_A: $i).
% 29.04/29.28  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 29.04/29.28  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 29.04/29.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 29.04/29.28  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 29.04/29.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.04/29.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.04/29.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.04/29.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.04/29.28  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 29.04/29.28  thf(sk_C_type, type, sk_C: $i).
% 29.04/29.28  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 29.04/29.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.04/29.28  thf(sk_D_type, type, sk_D: $i).
% 29.04/29.28  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 29.04/29.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.04/29.28  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 29.04/29.28  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 29.04/29.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.04/29.28  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 29.04/29.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 29.04/29.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 29.04/29.28  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 29.04/29.28  thf(sk_B_type, type, sk_B: $i).
% 29.04/29.28  thf(t55_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ( v2_funct_1 @ A ) =>
% 29.04/29.28         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 29.04/29.28           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 29.04/29.28  thf('0', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf(dt_k2_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 29.04/29.28         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 29.04/29.28  thf('1', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('2', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('3', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('4', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf(t36_funct_2, conjecture,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.04/29.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.04/29.28       ( ![D:$i]:
% 29.04/29.28         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 29.04/29.28             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 29.04/29.28           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 29.04/29.28               ( r2_relset_1 @
% 29.04/29.28                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 29.04/29.28                 ( k6_partfun1 @ A ) ) & 
% 29.04/29.28               ( v2_funct_1 @ C ) ) =>
% 29.04/29.28             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.04/29.28               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 29.04/29.28  thf(zf_stmt_0, negated_conjecture,
% 29.04/29.28    (~( ![A:$i,B:$i,C:$i]:
% 29.04/29.28        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.04/29.28            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.04/29.28          ( ![D:$i]:
% 29.04/29.28            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 29.04/29.28                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 29.04/29.28              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 29.04/29.28                  ( r2_relset_1 @
% 29.04/29.28                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 29.04/29.28                    ( k6_partfun1 @ A ) ) & 
% 29.04/29.28                  ( v2_funct_1 @ C ) ) =>
% 29.04/29.28                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.04/29.28                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 29.04/29.28    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 29.04/29.28  thf('5', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('6', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(redefinition_k1_partfun1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 29.04/29.28     ( ( ( v1_funct_1 @ E ) & 
% 29.04/29.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 29.04/29.28         ( v1_funct_1 @ F ) & 
% 29.04/29.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 29.04/29.28       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 29.04/29.28  thf('7', plain,
% 29.04/29.28      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 29.04/29.28          | ~ (v1_funct_1 @ X43)
% 29.04/29.28          | ~ (v1_funct_1 @ X46)
% 29.04/29.28          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 29.04/29.28          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 29.04/29.28              = (k5_relat_1 @ X43 @ X46)))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 29.04/29.28  thf('8', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 29.04/29.28            = (k5_relat_1 @ sk_C @ X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['6', '7'])).
% 29.04/29.28  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('10', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 29.04/29.28            = (k5_relat_1 @ sk_C @ X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 29.04/29.28          | ~ (v1_funct_1 @ X0))),
% 29.04/29.28      inference('demod', [status(thm)], ['8', '9'])).
% 29.04/29.28  thf('11', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 29.04/29.28            = (k5_relat_1 @ sk_C @ sk_D)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['5', '10'])).
% 29.04/29.28  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('13', plain,
% 29.04/29.28      ((r2_relset_1 @ sk_A @ sk_A @ 
% 29.04/29.28        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 29.04/29.28        (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('14', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('15', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(dt_k1_partfun1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 29.04/29.28     ( ( ( v1_funct_1 @ E ) & 
% 29.04/29.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 29.04/29.28         ( v1_funct_1 @ F ) & 
% 29.04/29.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 29.04/29.28       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 29.04/29.28         ( m1_subset_1 @
% 29.04/29.28           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 29.04/29.28           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 29.04/29.28  thf('16', plain,
% 29.04/29.28      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 29.04/29.28          | ~ (v1_funct_1 @ X35)
% 29.04/29.28          | ~ (v1_funct_1 @ X38)
% 29.04/29.28          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 29.04/29.28          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 29.04/29.28             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 29.04/29.28  thf('17', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 29.04/29.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 29.04/29.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 29.04/29.28          | ~ (v1_funct_1 @ X1)
% 29.04/29.28          | ~ (v1_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['15', '16'])).
% 29.04/29.28  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('19', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 29.04/29.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 29.04/29.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 29.04/29.28          | ~ (v1_funct_1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['17', '18'])).
% 29.04/29.28  thf('20', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | (m1_subset_1 @ 
% 29.04/29.28           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 29.04/29.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['14', '19'])).
% 29.04/29.28  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('22', plain,
% 29.04/29.28      ((m1_subset_1 @ 
% 29.04/29.28        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 29.04/29.28        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 29.04/29.28      inference('demod', [status(thm)], ['20', '21'])).
% 29.04/29.28  thf(redefinition_r2_relset_1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i,D:$i]:
% 29.04/29.28     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 29.04/29.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.04/29.28       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 29.04/29.28  thf('23', plain,
% 29.04/29.28      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | ((X23) = (X26))
% 29.04/29.28          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 29.04/29.28  thf('24', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 29.04/29.28             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 29.04/29.28          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['22', '23'])).
% 29.04/29.28  thf('25', plain,
% 29.04/29.28      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 29.04/29.28        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 29.04/29.28            = (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['13', '24'])).
% 29.04/29.28  thf(dt_k6_partfun1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( m1_subset_1 @
% 29.04/29.28         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 29.04/29.28       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 29.04/29.28  thf('26', plain,
% 29.04/29.28      (![X42 : $i]:
% 29.04/29.28         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 29.04/29.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 29.04/29.28  thf('27', plain,
% 29.04/29.28      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 29.04/29.28         = (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['25', '26'])).
% 29.04/29.28  thf('28', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['11', '12', '27'])).
% 29.04/29.28  thf(t66_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ![B:$i]:
% 29.04/29.28         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.04/29.28           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 29.04/29.28             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 29.04/29.28               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 29.04/29.28  thf('29', plain,
% 29.04/29.28      (![X11 : $i, X12 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X11)
% 29.04/29.28          | ~ (v1_funct_1 @ X11)
% 29.04/29.28          | ((k2_funct_1 @ (k5_relat_1 @ X12 @ X11))
% 29.04/29.28              = (k5_relat_1 @ (k2_funct_1 @ X11) @ (k2_funct_1 @ X12)))
% 29.04/29.28          | ~ (v2_funct_1 @ X11)
% 29.04/29.28          | ~ (v2_funct_1 @ X12)
% 29.04/29.28          | ~ (v1_funct_1 @ X12)
% 29.04/29.28          | ~ (v1_relat_1 @ X12))),
% 29.04/29.28      inference('cnf', [status(esa)], [t66_funct_1])).
% 29.04/29.28  thf(t64_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ![B:$i]:
% 29.04/29.28         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.04/29.28           ( ( ( v2_funct_1 @ A ) & 
% 29.04/29.28               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 29.04/29.28               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 29.04/29.28             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 29.04/29.28  thf('30', plain,
% 29.04/29.28      (![X8 : $i, X9 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X8)
% 29.04/29.28          | ~ (v1_funct_1 @ X8)
% 29.04/29.28          | ((X8) = (k2_funct_1 @ X9))
% 29.04/29.28          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 29.04/29.28          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 29.04/29.28          | ~ (v2_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_relat_1 @ X9))),
% 29.04/29.28      inference('cnf', [status(esa)], [t64_funct_1])).
% 29.04/29.28  thf(redefinition_k6_partfun1, axiom,
% 29.04/29.28    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 29.04/29.28  thf('31', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('32', plain,
% 29.04/29.28      (![X8 : $i, X9 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X8)
% 29.04/29.28          | ~ (v1_funct_1 @ X8)
% 29.04/29.28          | ((X8) = (k2_funct_1 @ X9))
% 29.04/29.28          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 29.04/29.28          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 29.04/29.28          | ~ (v2_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_relat_1 @ X9))),
% 29.04/29.28      inference('demod', [status(thm)], ['30', '31'])).
% 29.04/29.28  thf('33', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i]:
% 29.04/29.28         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 29.04/29.28            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X1))))
% 29.04/29.28          | ~ (v1_relat_1 @ X1)
% 29.04/29.28          | ~ (v1_funct_1 @ X1)
% 29.04/29.28          | ~ (v2_funct_1 @ X1)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 29.04/29.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X1))
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X1))
% 29.04/29.28          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28              != (k1_relat_1 @ (k2_funct_1 @ X1)))
% 29.04/29.28          | ((k2_funct_1 @ X0) = (k2_funct_1 @ (k2_funct_1 @ X1)))
% 29.04/29.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['29', '32'])).
% 29.04/29.28  thf('34', plain,
% 29.04/29.28      ((((k2_funct_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28            != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['28', '33'])).
% 29.04/29.28  thf(t67_funct_1, axiom,
% 29.04/29.28    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 29.04/29.28  thf('35', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X13)) = (k6_relat_1 @ X13))),
% 29.04/29.28      inference('cnf', [status(esa)], [t67_funct_1])).
% 29.04/29.28  thf('36', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('37', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('38', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X13)) = (k6_partfun1 @ X13))),
% 29.04/29.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 29.04/29.28  thf('39', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('40', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('41', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('42', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('43', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf(t61_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ( v2_funct_1 @ A ) =>
% 29.04/29.28         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 29.04/29.28             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 29.04/29.28           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 29.04/29.28             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 29.04/29.28  thf('44', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 29.04/29.28              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('cnf', [status(esa)], [t61_funct_1])).
% 29.04/29.28  thf('45', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('46', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 29.04/29.28              = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('demod', [status(thm)], ['44', '45'])).
% 29.04/29.28  thf(fc6_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 29.04/29.28       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 29.04/29.28         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 29.04/29.28         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 29.04/29.28  thf('47', plain,
% 29.04/29.28      (![X3 : $i]:
% 29.04/29.28         ((v2_funct_1 @ (k2_funct_1 @ X3))
% 29.04/29.28          | ~ (v2_funct_1 @ X3)
% 29.04/29.28          | ~ (v1_funct_1 @ X3)
% 29.04/29.28          | ~ (v1_relat_1 @ X3))),
% 29.04/29.28      inference('cnf', [status(esa)], [fc6_funct_1])).
% 29.04/29.28  thf('48', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('49', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf(t65_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 29.04/29.28  thf('50', plain,
% 29.04/29.28      (![X10 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X10)
% 29.04/29.28          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 29.04/29.28          | ~ (v1_funct_1 @ X10)
% 29.04/29.28          | ~ (v1_relat_1 @ X10))),
% 29.04/29.28      inference('cnf', [status(esa)], [t65_funct_1])).
% 29.04/29.28  thf('51', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 29.04/29.28              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('cnf', [status(esa)], [t61_funct_1])).
% 29.04/29.28  thf('52', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('53', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 29.04/29.28              = (k6_partfun1 @ (k2_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('demod', [status(thm)], ['51', '52'])).
% 29.04/29.28  thf('54', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 29.04/29.28      inference('sup+', [status(thm)], ['50', '53'])).
% 29.04/29.28  thf('55', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['49', '54'])).
% 29.04/29.28  thf('56', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['55'])).
% 29.04/29.28  thf('57', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['48', '56'])).
% 29.04/29.28  thf('58', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['57'])).
% 29.04/29.28  thf('59', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['47', '58'])).
% 29.04/29.28  thf('60', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['59'])).
% 29.04/29.28  thf('61', plain,
% 29.04/29.28      (![X42 : $i]:
% 29.04/29.28         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 29.04/29.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 29.04/29.28  thf('62', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 29.04/29.28           (k1_zfmisc_1 @ 
% 29.04/29.28            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 29.04/29.28             (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0))),
% 29.04/29.28      inference('sup+', [status(thm)], ['60', '61'])).
% 29.04/29.28  thf('63', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('64', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(d1_funct_2, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.28       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.04/29.28           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 29.04/29.28             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 29.04/29.28         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.04/29.28           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 29.04/29.28             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 29.04/29.28  thf(zf_stmt_1, axiom,
% 29.04/29.28    (![C:$i,B:$i,A:$i]:
% 29.04/29.28     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 29.04/29.28       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 29.04/29.28  thf('66', plain,
% 29.04/29.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 29.04/29.28         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 29.04/29.28          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 29.04/29.28          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.04/29.28  thf('67', plain,
% 29.04/29.28      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 29.04/29.28        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['65', '66'])).
% 29.04/29.28  thf(zf_stmt_2, axiom,
% 29.04/29.28    (![B:$i,A:$i]:
% 29.04/29.28     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.04/29.28       ( zip_tseitin_0 @ B @ A ) ))).
% 29.04/29.28  thf('68', plain,
% 29.04/29.28      (![X27 : $i, X28 : $i]:
% 29.04/29.28         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_2])).
% 29.04/29.28  thf('69', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 29.04/29.28  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 29.04/29.28  thf(zf_stmt_5, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.28       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 29.04/29.28         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.04/29.28           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 29.04/29.28             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 29.04/29.28  thf('70', plain,
% 29.04/29.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 29.04/29.28         (~ (zip_tseitin_0 @ X32 @ X33)
% 29.04/29.28          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 29.04/29.28          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.04/29.28  thf('71', plain,
% 29.04/29.28      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 29.04/29.28      inference('sup-', [status(thm)], ['69', '70'])).
% 29.04/29.28  thf('72', plain,
% 29.04/29.28      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 29.04/29.28      inference('sup-', [status(thm)], ['68', '71'])).
% 29.04/29.28  thf('73', plain, (((sk_B) != (k1_xboole_0))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('74', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 29.04/29.28      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 29.04/29.28  thf('75', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(redefinition_k1_relset_1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.28       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 29.04/29.28  thf('76', plain,
% 29.04/29.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 29.04/29.28         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 29.04/29.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.04/29.28  thf('77', plain,
% 29.04/29.28      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['75', '76'])).
% 29.04/29.28  thf('78', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('79', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 29.04/29.28              = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('demod', [status(thm)], ['44', '45'])).
% 29.04/29.28  thf('80', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['59'])).
% 29.04/29.28  thf(fc4_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 29.04/29.28       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 29.04/29.28  thf('81', plain, (![X1 : $i]: (v1_relat_1 @ (k6_relat_1 @ X1))),
% 29.04/29.28      inference('cnf', [status(esa)], [fc4_funct_1])).
% 29.04/29.28  thf('82', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('83', plain, (![X1 : $i]: (v1_relat_1 @ (k6_partfun1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['81', '82'])).
% 29.04/29.28  thf('84', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0))),
% 29.04/29.28      inference('sup+', [status(thm)], ['80', '83'])).
% 29.04/29.28  thf('85', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['59'])).
% 29.04/29.28  thf('86', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X13)) = (k6_partfun1 @ X13))),
% 29.04/29.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 29.04/29.28  thf('87', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k2_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0))),
% 29.04/29.28      inference('sup+', [status(thm)], ['85', '86'])).
% 29.04/29.28  thf('88', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('89', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 29.04/29.28          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))),
% 29.04/29.28      inference('sup+', [status(thm)], ['87', '88'])).
% 29.04/29.28  thf('90', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['84', '89'])).
% 29.04/29.28  thf('91', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0))),
% 29.04/29.28      inference('simplify', [status(thm)], ['90'])).
% 29.04/29.28  thf('92', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['79', '91'])).
% 29.04/29.28  thf('93', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 29.04/29.28          | ~ (v2_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 29.04/29.28      inference('simplify', [status(thm)], ['92'])).
% 29.04/29.28  thf('94', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['78', '93'])).
% 29.04/29.28  thf('95', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('96', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('97', plain,
% 29.04/29.28      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 29.04/29.28          | ~ (v1_funct_1 @ X35)
% 29.04/29.28          | ~ (v1_funct_1 @ X38)
% 29.04/29.28          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 29.04/29.28          | (v1_funct_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 29.04/29.28  thf('98', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['96', '97'])).
% 29.04/29.28  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('100', plain,
% 29.04/29.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 29.04/29.28          | ~ (v1_funct_1 @ X0))),
% 29.04/29.28      inference('demod', [status(thm)], ['98', '99'])).
% 29.04/29.28  thf('101', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['95', '100'])).
% 29.04/29.28  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('103', plain,
% 29.04/29.28      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['101', '102'])).
% 29.04/29.28  thf('104', plain,
% 29.04/29.28      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 29.04/29.28         = (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['25', '26'])).
% 29.04/29.28  thf('105', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['103', '104'])).
% 29.04/29.28  thf('106', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(cc1_relset_1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.28       ( v1_relat_1 @ C ) ))).
% 29.04/29.28  thf('107', plain,
% 29.04/29.28      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.04/29.28         ((v1_relat_1 @ X14)
% 29.04/29.28          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 29.04/29.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 29.04/29.28  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('111', plain,
% 29.04/29.28      ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['94', '105', '108', '109', '110'])).
% 29.04/29.28  thf('112', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X13)) = (k6_partfun1 @ X13))),
% 29.04/29.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 29.04/29.28  thf('113', plain,
% 29.04/29.28      (![X7 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X7)
% 29.04/29.28          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 29.04/29.28              = (k6_partfun1 @ (k2_relat_1 @ X7)))
% 29.04/29.28          | ~ (v1_funct_1 @ X7)
% 29.04/29.28          | ~ (v1_relat_1 @ X7))),
% 29.04/29.28      inference('demod', [status(thm)], ['51', '52'])).
% 29.04/29.28  thf('114', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0))))
% 29.04/29.28          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 29.04/29.28      inference('sup+', [status(thm)], ['112', '113'])).
% 29.04/29.28  thf('115', plain, (![X1 : $i]: (v1_relat_1 @ (k6_partfun1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['81', '82'])).
% 29.04/29.28  thf('116', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 29.04/29.28      inference('cnf', [status(esa)], [fc4_funct_1])).
% 29.04/29.28  thf('117', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.04/29.28  thf('118', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 29.04/29.28      inference('demod', [status(thm)], ['116', '117'])).
% 29.04/29.28  thf('119', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0))))
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 29.04/29.28      inference('demod', [status(thm)], ['114', '115', '118'])).
% 29.04/29.28  thf('120', plain,
% 29.04/29.28      (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 29.04/29.28         (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k6_partfun1 @ 
% 29.04/29.28            (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['111', '119'])).
% 29.04/29.28  thf('121', plain,
% 29.04/29.28      ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['94', '105', '108', '109', '110'])).
% 29.04/29.28  thf('122', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X13)) = (k6_partfun1 @ X13))),
% 29.04/29.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 29.04/29.28  thf('123', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('124', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 29.04/29.28            = (k2_relat_1 @ (k6_partfun1 @ X0)))
% 29.04/29.28          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 29.04/29.28          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 29.04/29.28      inference('sup+', [status(thm)], ['122', '123'])).
% 29.04/29.28  thf('125', plain, (![X1 : $i]: (v1_relat_1 @ (k6_partfun1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['81', '82'])).
% 29.04/29.28  thf('126', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 29.04/29.28      inference('demod', [status(thm)], ['116', '117'])).
% 29.04/29.28  thf('127', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 29.04/29.28            = (k2_relat_1 @ (k6_partfun1 @ X0)))
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 29.04/29.28      inference('demod', [status(thm)], ['124', '125', '126'])).
% 29.04/29.28  thf('128', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['121', '127'])).
% 29.04/29.28  thf('129', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('130', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['121', '127'])).
% 29.04/29.28  thf('131', plain,
% 29.04/29.28      ((((k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28          = (k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup+', [status(thm)], ['129', '130'])).
% 29.04/29.28  thf('132', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('133', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['103', '104'])).
% 29.04/29.28  thf('134', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 29.04/29.28            = (k2_relat_1 @ (k6_partfun1 @ X0)))
% 29.04/29.28          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 29.04/29.28      inference('demod', [status(thm)], ['124', '125', '126'])).
% 29.04/29.28  thf('135', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['133', '134'])).
% 29.04/29.28  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('139', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k1_relat_1 @ (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['131', '132', '135', '136', '137', '138'])).
% 29.04/29.28  thf('140', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('demod', [status(thm)], ['128', '139'])).
% 29.04/29.28  thf('141', plain,
% 29.04/29.28      (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 29.04/29.28         (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A))))),
% 29.04/29.28      inference('demod', [status(thm)], ['120', '140'])).
% 29.04/29.28  thf('142', plain,
% 29.04/29.28      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 29.04/29.28          (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28          = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A))))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup+', [status(thm)], ['64', '141'])).
% 29.04/29.28  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('147', plain,
% 29.04/29.28      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28         (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A))))),
% 29.04/29.28      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 29.04/29.28  thf('148', plain,
% 29.04/29.28      (![X8 : $i, X9 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X8)
% 29.04/29.28          | ~ (v1_funct_1 @ X8)
% 29.04/29.28          | ((X8) = (k2_funct_1 @ X9))
% 29.04/29.28          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 29.04/29.28          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 29.04/29.28          | ~ (v2_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_relat_1 @ X9))),
% 29.04/29.28      inference('demod', [status(thm)], ['30', '31'])).
% 29.04/29.28  thf('149', plain,
% 29.04/29.28      ((((k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 29.04/29.28          != (k6_partfun1 @ 
% 29.04/29.28              (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))
% 29.04/29.28        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28        | ~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28        | ~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28        | ((k2_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28            != (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 29.04/29.28        | ((k6_partfun1 @ sk_A)
% 29.04/29.28            = (k2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 29.04/29.28        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['147', '148'])).
% 29.04/29.28  thf('150', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('demod', [status(thm)], ['128', '139'])).
% 29.04/29.28  thf('151', plain, (![X1 : $i]: (v1_relat_1 @ (k6_partfun1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['81', '82'])).
% 29.04/29.28  thf('152', plain,
% 29.04/29.28      ((v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['94', '105', '108', '109', '110'])).
% 29.04/29.28  thf('153', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 29.04/29.28      inference('demod', [status(thm)], ['116', '117'])).
% 29.04/29.28  thf('154', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28         = (k2_relat_1 @ (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['133', '134'])).
% 29.04/29.28  thf('155', plain,
% 29.04/29.28      (((k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28         = (k1_relat_1 @ (k6_partfun1 @ sk_A)))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['131', '132', '135', '136', '137', '138'])).
% 29.04/29.28  thf('156', plain,
% 29.04/29.28      (![X13 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X13)) = (k6_partfun1 @ X13))),
% 29.04/29.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 29.04/29.28  thf('157', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['103', '104'])).
% 29.04/29.28  thf('158', plain, (![X1 : $i]: (v1_relat_1 @ (k6_partfun1 @ X1))),
% 29.04/29.28      inference('demod', [status(thm)], ['81', '82'])).
% 29.04/29.28  thf('159', plain,
% 29.04/29.28      ((((k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 29.04/29.28          != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ sk_A))))
% 29.04/29.28        | ((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28            != (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 29.04/29.28        | ((k6_partfun1 @ sk_A)
% 29.04/29.28            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['149', '150', '151', '152', '153', '154', '155', '156', 
% 29.04/29.28                 '157', '158'])).
% 29.04/29.28  thf('160', plain,
% 29.04/29.28      (((k6_partfun1 @ sk_A)
% 29.04/29.28         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('simplify', [status(thm)], ['159'])).
% 29.04/29.28  thf('161', plain,
% 29.04/29.28      (![X42 : $i]:
% 29.04/29.28         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 29.04/29.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 29.04/29.28  thf('162', plain,
% 29.04/29.28      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28        (k1_zfmisc_1 @ 
% 29.04/29.28         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('sup+', [status(thm)], ['160', '161'])).
% 29.04/29.28  thf('163', plain,
% 29.04/29.28      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | ((X23) = (X26))
% 29.04/29.28          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 29.04/29.28  thf('164', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (r2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28             (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_A) @ X0)
% 29.04/29.28          | ((k6_partfun1 @ sk_A) = (X0))
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ 
% 29.04/29.28               (k1_zfmisc_1 @ 
% 29.04/29.28                (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28                 (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['162', '163'])).
% 29.04/29.28  thf('165', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (r2_relset_1 @ (k1_relat_1 @ sk_C) @ 
% 29.04/29.28             (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_A) @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28          | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28          | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ 
% 29.04/29.28               (k1_zfmisc_1 @ 
% 29.04/29.28                (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28                 (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 29.04/29.28          | ((k6_partfun1 @ sk_A) = (X0)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['63', '164'])).
% 29.04/29.28  thf('166', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('170', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         (~ (r2_relset_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28             (k6_partfun1 @ sk_A) @ X0)
% 29.04/29.28          | ~ (m1_subset_1 @ X0 @ 
% 29.04/29.28               (k1_zfmisc_1 @ 
% 29.04/29.28                (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28                 (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 29.04/29.28          | ((k6_partfun1 @ sk_A) = (X0)))),
% 29.04/29.28      inference('demod', [status(thm)], ['165', '166', '167', '168', '169'])).
% 29.04/29.28  thf('171', plain,
% 29.04/29.28      ((~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (r2_relset_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28             (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['62', '170'])).
% 29.04/29.28  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('175', plain,
% 29.04/29.28      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (r2_relset_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28             (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 29.04/29.28  thf('176', plain,
% 29.04/29.28      ((~ (r2_relset_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28           (k6_partfun1 @ sk_A) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['46', '175'])).
% 29.04/29.28  thf('177', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('178', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('179', plain,
% 29.04/29.28      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28        (k1_zfmisc_1 @ 
% 29.04/29.28         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('sup+', [status(thm)], ['160', '161'])).
% 29.04/29.28  thf('180', plain,
% 29.04/29.28      (((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28         (k1_zfmisc_1 @ 
% 29.04/29.28          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 29.04/29.28           (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C))),
% 29.04/29.28      inference('sup+', [status(thm)], ['178', '179'])).
% 29.04/29.28  thf('181', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('185', plain,
% 29.04/29.28      ((m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 29.04/29.28        (k1_zfmisc_1 @ 
% 29.04/29.28         (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.04/29.28      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 29.04/29.28  thf('186', plain,
% 29.04/29.28      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 29.04/29.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.04/29.28          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 29.04/29.28          | ((X23) != (X26)))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 29.04/29.28  thf('187', plain,
% 29.04/29.28      (![X24 : $i, X25 : $i, X26 : $i]:
% 29.04/29.28         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 29.04/29.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 29.04/29.28      inference('simplify', [status(thm)], ['186'])).
% 29.04/29.28  thf('188', plain,
% 29.04/29.28      ((r2_relset_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 29.04/29.28        (k6_partfun1 @ sk_A) @ (k6_partfun1 @ sk_A))),
% 29.04/29.28      inference('sup-', [status(thm)], ['185', '187'])).
% 29.04/29.28  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('192', plain,
% 29.04/29.28      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['176', '177', '188', '189', '190', '191'])).
% 29.04/29.28  thf('193', plain,
% 29.04/29.28      (![X8 : $i, X9 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X8)
% 29.04/29.28          | ~ (v1_funct_1 @ X8)
% 29.04/29.28          | ((X8) = (k2_funct_1 @ X9))
% 29.04/29.28          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 29.04/29.28          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 29.04/29.28          | ~ (v2_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_funct_1 @ X9)
% 29.04/29.28          | ~ (v1_relat_1 @ X9))),
% 29.04/29.28      inference('demod', [status(thm)], ['30', '31'])).
% 29.04/29.28  thf('194', plain,
% 29.04/29.28      ((((k6_partfun1 @ sk_A)
% 29.04/29.28          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['192', '193'])).
% 29.04/29.28  thf('195', plain,
% 29.04/29.28      (((k6_partfun1 @ sk_A)
% 29.04/29.28         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('simplify', [status(thm)], ['159'])).
% 29.04/29.28  thf('196', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf(redefinition_k2_relset_1, axiom,
% 29.04/29.28    (![A:$i,B:$i,C:$i]:
% 29.04/29.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.28       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 29.04/29.28  thf('197', plain,
% 29.04/29.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 29.04/29.28         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 29.04/29.28          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.04/29.28  thf('198', plain,
% 29.04/29.28      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['196', '197'])).
% 29.04/29.28  thf('199', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('200', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('203', plain,
% 29.04/29.28      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['194', '195', '200', '201', '202'])).
% 29.04/29.28  thf('204', plain,
% 29.04/29.28      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('simplify', [status(thm)], ['203'])).
% 29.04/29.28  thf('205', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('206', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('207', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('208', plain,
% 29.04/29.28      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['176', '177', '188', '189', '190', '191'])).
% 29.04/29.28  thf(t48_funct_1, axiom,
% 29.04/29.28    (![A:$i]:
% 29.04/29.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.28       ( ![B:$i]:
% 29.04/29.28         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.04/29.28           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 29.04/29.28               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 29.04/29.28             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 29.04/29.28  thf('209', plain,
% 29.04/29.28      (![X4 : $i, X5 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X4)
% 29.04/29.28          | ~ (v1_funct_1 @ X4)
% 29.04/29.28          | (v2_funct_1 @ X5)
% 29.04/29.28          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 29.04/29.28          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 29.04/29.28          | ~ (v1_funct_1 @ X5)
% 29.04/29.28          | ~ (v1_relat_1 @ X5))),
% 29.04/29.28      inference('cnf', [status(esa)], [t48_funct_1])).
% 29.04/29.28  thf('210', plain,
% 29.04/29.28      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['208', '209'])).
% 29.04/29.28  thf('211', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 29.04/29.28      inference('demod', [status(thm)], ['116', '117'])).
% 29.04/29.28  thf('212', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('215', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['210', '211', '212', '213', '214'])).
% 29.04/29.28  thf('216', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['207', '215'])).
% 29.04/29.28  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('219', plain,
% 29.04/29.28      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['216', '217', '218'])).
% 29.04/29.28  thf('220', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['206', '219'])).
% 29.04/29.28  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('222', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('223', plain,
% 29.04/29.28      ((((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['220', '221', '222'])).
% 29.04/29.28  thf('224', plain,
% 29.04/29.28      ((((sk_B) != (k2_relat_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['205', '223'])).
% 29.04/29.28  thf('225', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('228', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('229', plain,
% 29.04/29.28      ((((sk_B) != (sk_B)) | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['224', '225', '226', '227', '228'])).
% 29.04/29.28  thf('230', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.04/29.28      inference('simplify', [status(thm)], ['229'])).
% 29.04/29.28  thf('231', plain,
% 29.04/29.28      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['204', '230'])).
% 29.04/29.28  thf('232', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['43', '231'])).
% 29.04/29.28  thf('233', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('235', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['232', '233', '234'])).
% 29.04/29.28  thf('236', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['42', '235'])).
% 29.04/29.28  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('239', plain,
% 29.04/29.28      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.04/29.28        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['236', '237', '238'])).
% 29.04/29.28  thf('240', plain,
% 29.04/29.28      ((((sk_B) != (k2_relat_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_C)
% 29.04/29.28        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('sup-', [status(thm)], ['41', '239'])).
% 29.04/29.28  thf('241', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('244', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('245', plain,
% 29.04/29.28      ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.04/29.28      inference('demod', [status(thm)], ['240', '241', '242', '243', '244'])).
% 29.04/29.28  thf('246', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('simplify', [status(thm)], ['245'])).
% 29.04/29.28  thf('247', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('248', plain,
% 29.04/29.28      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup+', [status(thm)], ['246', '247'])).
% 29.04/29.28  thf('249', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 29.04/29.28      inference('demod', [status(thm)], ['67', '74', '77'])).
% 29.04/29.28  thf('250', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.04/29.28      inference('simplify', [status(thm)], ['229'])).
% 29.04/29.28  thf('251', plain,
% 29.04/29.28      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['248', '249', '250'])).
% 29.04/29.28  thf('252', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['40', '251'])).
% 29.04/29.28  thf('253', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('254', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('255', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 29.04/29.28      inference('demod', [status(thm)], ['252', '253', '254'])).
% 29.04/29.28  thf('256', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['39', '255'])).
% 29.04/29.28  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('259', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 29.04/29.28      inference('demod', [status(thm)], ['256', '257', '258'])).
% 29.04/29.28  thf('260', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('simplify', [status(thm)], ['245'])).
% 29.04/29.28  thf('261', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('262', plain,
% 29.04/29.28      (![X0 : $i]:
% 29.04/29.28         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 29.04/29.28          | ~ (v1_funct_1 @ X0)
% 29.04/29.28          | ~ (v1_relat_1 @ X0))),
% 29.04/29.28      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 29.04/29.28  thf('263', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('simplify', [status(thm)], ['245'])).
% 29.04/29.28  thf('264', plain,
% 29.04/29.28      (![X6 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X6)
% 29.04/29.28          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 29.04/29.28          | ~ (v1_funct_1 @ X6)
% 29.04/29.28          | ~ (v1_relat_1 @ X6))),
% 29.04/29.28      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.04/29.28  thf('265', plain,
% 29.04/29.28      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup+', [status(thm)], ['263', '264'])).
% 29.04/29.28  thf('266', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('267', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.04/29.28      inference('simplify', [status(thm)], ['229'])).
% 29.04/29.28  thf('268', plain,
% 29.04/29.28      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['265', '266', '267'])).
% 29.04/29.28  thf('269', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['262', '268'])).
% 29.04/29.28  thf('270', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('271', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('272', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B)))),
% 29.04/29.28      inference('demod', [status(thm)], ['269', '270', '271'])).
% 29.04/29.28  thf('273', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['261', '272'])).
% 29.04/29.28  thf('274', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('276', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 29.04/29.28      inference('demod', [status(thm)], ['273', '274', '275'])).
% 29.04/29.28  thf('277', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.04/29.28      inference('simplify', [status(thm)], ['229'])).
% 29.04/29.28  thf('278', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('279', plain,
% 29.04/29.28      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.04/29.28         ((v1_relat_1 @ X14)
% 29.04/29.28          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 29.04/29.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 29.04/29.28  thf('280', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('281', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('282', plain, ((v2_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('283', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('284', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('285', plain,
% 29.04/29.28      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v2_funct_1 @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['34', '38', '259', '260', '276', '277', '280', '281', '282', 
% 29.04/29.28                 '283', '284'])).
% 29.04/29.28  thf('286', plain,
% 29.04/29.28      ((~ (v2_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 29.04/29.28      inference('simplify', [status(thm)], ['285'])).
% 29.04/29.28  thf('287', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['11', '12', '27'])).
% 29.04/29.28  thf('288', plain,
% 29.04/29.28      (![X4 : $i, X5 : $i]:
% 29.04/29.28         (~ (v1_relat_1 @ X4)
% 29.04/29.28          | ~ (v1_funct_1 @ X4)
% 29.04/29.28          | (v2_funct_1 @ X5)
% 29.04/29.28          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 29.04/29.28          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 29.04/29.28          | ~ (v1_funct_1 @ X5)
% 29.04/29.28          | ~ (v1_relat_1 @ X5))),
% 29.04/29.28      inference('cnf', [status(esa)], [t48_funct_1])).
% 29.04/29.28  thf('289', plain,
% 29.04/29.28      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 29.04/29.28        | (v2_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ sk_C))),
% 29.04/29.28      inference('sup-', [status(thm)], ['287', '288'])).
% 29.04/29.28  thf('290', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 29.04/29.28      inference('demod', [status(thm)], ['116', '117'])).
% 29.04/29.28  thf('291', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('292', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('293', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 29.04/29.28      inference('sup+', [status(thm)], ['198', '199'])).
% 29.04/29.28  thf('294', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('295', plain,
% 29.04/29.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 29.04/29.28         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 29.04/29.28          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 29.04/29.28          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.04/29.28  thf('296', plain,
% 29.04/29.28      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 29.04/29.28        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['294', '295'])).
% 29.04/29.28  thf('297', plain,
% 29.04/29.28      (![X27 : $i, X28 : $i]:
% 29.04/29.28         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_2])).
% 29.04/29.28  thf('298', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('299', plain,
% 29.04/29.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 29.04/29.28         (~ (zip_tseitin_0 @ X32 @ X33)
% 29.04/29.28          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 29.04/29.28          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.04/29.28  thf('300', plain,
% 29.04/29.28      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 29.04/29.28      inference('sup-', [status(thm)], ['298', '299'])).
% 29.04/29.28  thf('301', plain,
% 29.04/29.28      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 29.04/29.28      inference('sup-', [status(thm)], ['297', '300'])).
% 29.04/29.28  thf('302', plain, (((sk_A) != (k1_xboole_0))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('303', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 29.04/29.28      inference('simplify_reflect-', [status(thm)], ['301', '302'])).
% 29.04/29.28  thf('304', plain,
% 29.04/29.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('305', plain,
% 29.04/29.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 29.04/29.28         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 29.04/29.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 29.04/29.28      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.04/29.28  thf('306', plain,
% 29.04/29.28      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 29.04/29.28      inference('sup-', [status(thm)], ['304', '305'])).
% 29.04/29.28  thf('307', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['296', '303', '306'])).
% 29.04/29.28  thf('308', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('309', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('310', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)],
% 29.04/29.28                ['289', '290', '291', '292', '293', '307', '308', '309'])).
% 29.04/29.28  thf('311', plain, ((v2_funct_1 @ sk_D)),
% 29.04/29.28      inference('simplify', [status(thm)], ['310'])).
% 29.04/29.28  thf('312', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 29.04/29.28      inference('demod', [status(thm)], ['286', '311'])).
% 29.04/29.28  thf('313', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['4', '312'])).
% 29.04/29.28  thf('314', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('316', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['313', '314', '315'])).
% 29.04/29.28  thf('317', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['3', '316'])).
% 29.04/29.28  thf('318', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('319', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('320', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D)))),
% 29.04/29.28      inference('demod', [status(thm)], ['317', '318', '319'])).
% 29.04/29.28  thf('321', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_C)
% 29.04/29.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['2', '320'])).
% 29.04/29.28  thf('322', plain, ((v1_relat_1 @ sk_C)),
% 29.04/29.28      inference('sup-', [status(thm)], ['106', '107'])).
% 29.04/29.28  thf('323', plain, ((v1_funct_1 @ sk_C)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('324', plain,
% 29.04/29.28      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C))
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 29.04/29.28      inference('demod', [status(thm)], ['321', '322', '323'])).
% 29.04/29.28  thf('325', plain,
% 29.04/29.28      ((~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['1', '324'])).
% 29.04/29.28  thf('326', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('327', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('328', plain,
% 29.04/29.28      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['325', '326', '327'])).
% 29.04/29.28  thf('329', plain,
% 29.04/29.28      ((((k1_relat_1 @ sk_D) != (sk_B))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_D)
% 29.04/29.28        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 29.04/29.28      inference('sup-', [status(thm)], ['0', '328'])).
% 29.04/29.28  thf('330', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['296', '303', '306'])).
% 29.04/29.28  thf('331', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('332', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('333', plain, ((v2_funct_1 @ sk_D)),
% 29.04/29.28      inference('simplify', [status(thm)], ['310'])).
% 29.04/29.28  thf('334', plain, ((((sk_B) != (sk_B)) | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 29.04/29.28      inference('demod', [status(thm)], ['329', '330', '331', '332', '333'])).
% 29.04/29.28  thf('335', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 29.04/29.28      inference('simplify', [status(thm)], ['334'])).
% 29.04/29.28  thf('336', plain,
% 29.04/29.28      (![X10 : $i]:
% 29.04/29.28         (~ (v2_funct_1 @ X10)
% 29.04/29.28          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 29.04/29.28          | ~ (v1_funct_1 @ X10)
% 29.04/29.28          | ~ (v1_relat_1 @ X10))),
% 29.04/29.28      inference('cnf', [status(esa)], [t65_funct_1])).
% 29.04/29.28  thf('337', plain,
% 29.04/29.28      ((((k2_funct_1 @ sk_C) = (sk_D))
% 29.04/29.28        | ~ (v1_relat_1 @ sk_D)
% 29.04/29.28        | ~ (v1_funct_1 @ sk_D)
% 29.04/29.28        | ~ (v2_funct_1 @ sk_D))),
% 29.04/29.28      inference('sup+', [status(thm)], ['335', '336'])).
% 29.04/29.28  thf('338', plain, ((v1_relat_1 @ sk_D)),
% 29.04/29.28      inference('sup-', [status(thm)], ['278', '279'])).
% 29.04/29.28  thf('339', plain, ((v1_funct_1 @ sk_D)),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('340', plain, ((v2_funct_1 @ sk_D)),
% 29.04/29.28      inference('simplify', [status(thm)], ['310'])).
% 29.04/29.28  thf('341', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 29.04/29.28      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 29.04/29.28  thf('342', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 29.04/29.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.28  thf('343', plain, ($false),
% 29.04/29.28      inference('simplify_reflect-', [status(thm)], ['341', '342'])).
% 29.04/29.28  
% 29.04/29.28  % SZS output end Refutation
% 29.04/29.28  
% 29.04/29.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
