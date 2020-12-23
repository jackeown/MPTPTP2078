%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q6v76Zcfnc

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:19 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  239 (4667 expanded)
%              Number of leaves         :   48 (1456 expanded)
%              Depth                    :   26
%              Number of atoms          : 2306 (99928 expanded)
%              Number of equality atoms :  180 (6920 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

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

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('27',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
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
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_partfun1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','53','54','59','60','65'])).

thf('67',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( zip_tseitin_0 @ X47 @ X50 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47 ) )
      | ( zip_tseitin_1 @ X49 @ X48 )
      | ( ( k2_relset_1 @ X51 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('82',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('86',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X14 @ X13 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('91',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X14 @ X13 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('95',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('98',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('102',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','96','97','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['75','104','105','106','107','108'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('112',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_funct_1 @ X44 )
      | ~ ( zip_tseitin_0 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','116'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('119',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('122',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('123',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('125',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('131',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('134',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('137',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('139',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('141',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('143',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['117','143'])).

thf('145',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('147',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('148',plain,(
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
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
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
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
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
    inference('sup-',[status(thm)],['145','149'])).

thf('151',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('153',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('154',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('156',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('158',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('163',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('164',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('167',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('182',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('184',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('186',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154','155','156','157','158','159','160','161','162','163','184','185'])).

thf('187',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['187','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q6v76Zcfnc
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:41 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.89/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.13  % Solved by: fo/fo7.sh
% 0.89/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.13  % done 826 iterations in 0.664s
% 0.89/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.13  % SZS output start Refutation
% 0.89/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.13  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.89/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.89/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.13  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.89/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.13  thf(t36_funct_2, conjecture,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13               ( r2_relset_1 @
% 0.89/1.13                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                 ( k6_partfun1 @ A ) ) & 
% 0.89/1.13               ( v2_funct_1 @ C ) ) =>
% 0.89/1.13             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.13    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.13        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13          ( ![D:$i]:
% 0.89/1.13            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13                  ( r2_relset_1 @
% 0.89/1.13                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                    ( k6_partfun1 @ A ) ) & 
% 0.89/1.13                  ( v2_funct_1 @ C ) ) =>
% 0.89/1.13                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.89/1.13    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.89/1.13  thf('0', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('1', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.13  thf('2', plain,
% 0.89/1.13      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.89/1.13          | ~ (v1_funct_1 @ X32)
% 0.89/1.13          | ~ (v1_funct_1 @ X35)
% 0.89/1.13          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.89/1.13          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.89/1.13              = (k5_relat_1 @ X32 @ X35)))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.89/1.13  thf('3', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.13  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('5', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['3', '4'])).
% 0.89/1.13  thf('6', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['0', '5'])).
% 0.89/1.13  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('8', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('9', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('10', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(dt_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.89/1.13         ( m1_subset_1 @
% 0.89/1.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.89/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.89/1.13  thf('11', plain,
% 0.89/1.13      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.89/1.13          | ~ (v1_funct_1 @ X26)
% 0.89/1.13          | ~ (v1_funct_1 @ X29)
% 0.89/1.13          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.89/1.13          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.89/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.89/1.13  thf('12', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.13  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('14', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1))),
% 0.89/1.13      inference('demod', [status(thm)], ['12', '13'])).
% 0.89/1.13  thf('15', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | (m1_subset_1 @ 
% 0.89/1.13           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['9', '14'])).
% 0.89/1.13  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('17', plain,
% 0.89/1.13      ((m1_subset_1 @ 
% 0.89/1.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['15', '16'])).
% 0.89/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.89/1.13  thf('18', plain,
% 0.89/1.13      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.89/1.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.89/1.13          | ((X21) = (X24))
% 0.89/1.13          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.13  thf('19', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.89/1.13          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.13  thf('20', plain,
% 0.89/1.13      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.89/1.13        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13            = (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['8', '19'])).
% 0.89/1.13  thf(t29_relset_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( m1_subset_1 @
% 0.89/1.13       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.89/1.13  thf('21', plain,
% 0.89/1.13      (![X25 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.89/1.13  thf(redefinition_k6_partfun1, axiom,
% 0.89/1.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.13  thf('22', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('23', plain,
% 0.89/1.13      (![X25 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.89/1.13      inference('demod', [status(thm)], ['21', '22'])).
% 0.89/1.13  thf('24', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['20', '23'])).
% 0.89/1.13  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['6', '7', '24'])).
% 0.89/1.13  thf(t64_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ A ) & 
% 0.89/1.13               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.89/1.13               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.89/1.13             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('26', plain,
% 0.89/1.13      (![X16 : $i, X17 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X16)
% 0.89/1.13          | ~ (v1_funct_1 @ X16)
% 0.89/1.13          | ((X16) = (k2_funct_1 @ X17))
% 0.89/1.13          | ((k5_relat_1 @ X16 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X17)))
% 0.89/1.13          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.89/1.13          | ~ (v2_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_relat_1 @ X17))),
% 0.89/1.13      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.89/1.13  thf('27', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('28', plain,
% 0.89/1.13      (![X16 : $i, X17 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X16)
% 0.89/1.13          | ~ (v1_funct_1 @ X16)
% 0.89/1.13          | ((X16) = (k2_funct_1 @ X17))
% 0.89/1.13          | ((k5_relat_1 @ X16 @ X17) != (k6_partfun1 @ (k2_relat_1 @ X17)))
% 0.89/1.13          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.89/1.13          | ~ (v2_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_relat_1 @ X17))),
% 0.89/1.13      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.13  thf('29', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['25', '28'])).
% 0.89/1.13  thf('30', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['20', '23'])).
% 0.89/1.13  thf('31', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t24_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( r2_relset_1 @
% 0.89/1.13               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.89/1.13               ( k6_partfun1 @ B ) ) =>
% 0.89/1.13             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.89/1.13  thf('32', plain,
% 0.89/1.13      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X39)
% 0.89/1.13          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.89/1.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.89/1.13          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 0.89/1.13               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 0.89/1.13               (k6_partfun1 @ X40))
% 0.89/1.13          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 0.89/1.13          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.89/1.13          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 0.89/1.13          | ~ (v1_funct_1 @ X42))),
% 0.89/1.13      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.89/1.13  thf('33', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A))
% 0.89/1.13          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.13  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('36', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.89/1.13  thf('37', plain,
% 0.89/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.89/1.13           (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.89/1.13        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['30', '36'])).
% 0.89/1.13  thf('38', plain,
% 0.89/1.13      (![X25 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.89/1.13      inference('demod', [status(thm)], ['21', '22'])).
% 0.89/1.13  thf('39', plain,
% 0.89/1.13      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.89/1.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.89/1.13          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 0.89/1.13          | ((X21) != (X24)))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.13  thf('40', plain,
% 0.89/1.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.13         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.89/1.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['39'])).
% 0.89/1.13  thf('41', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['38', '40'])).
% 0.89/1.13  thf('42', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.13  thf('43', plain,
% 0.89/1.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.89/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('44', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.13  thf('45', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.89/1.13  thf('49', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(cc2_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ A ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.13  thf('50', plain,
% 0.89/1.13      (![X3 : $i, X4 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.89/1.13          | (v1_relat_1 @ X3)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.13  thf('51', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.13  thf(fc6_relat_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.13  thf('52', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.13  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('55', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('56', plain,
% 0.89/1.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.89/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('57', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['55', '56'])).
% 0.89/1.13  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['57', '58'])).
% 0.89/1.13  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('61', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('62', plain,
% 0.89/1.13      (![X3 : $i, X4 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.89/1.13          | (v1_relat_1 @ X3)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.13  thf('63', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['61', '62'])).
% 0.89/1.13  thf('64', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.13  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('demod', [status(thm)], ['63', '64'])).
% 0.89/1.13  thf('66', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['29', '48', '53', '54', '59', '60', '65'])).
% 0.89/1.13  thf('67', plain,
% 0.89/1.13      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.89/1.13        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['66'])).
% 0.89/1.13  thf('68', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['20', '23'])).
% 0.89/1.13  thf('69', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t30_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.89/1.13       ( ![E:$i]:
% 0.89/1.13         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.89/1.13             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.89/1.13           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.89/1.13               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.89/1.13             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.89/1.13               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_2, axiom,
% 0.89/1.13    (![C:$i,B:$i]:
% 0.89/1.13     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.89/1.13       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_4, axiom,
% 0.89/1.13    (![E:$i,D:$i]:
% 0.89/1.13     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.89/1.13  thf(zf_stmt_5, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![E:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.89/1.13             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.89/1.13               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.89/1.13             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.89/1.13  thf('70', plain,
% 0.89/1.13      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X47)
% 0.89/1.13          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.89/1.13          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.89/1.13          | (zip_tseitin_0 @ X47 @ X50)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47))
% 0.89/1.13          | (zip_tseitin_1 @ X49 @ X48)
% 0.89/1.13          | ((k2_relset_1 @ X51 @ X48 @ X50) != (X48))
% 0.89/1.13          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 0.89/1.13          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 0.89/1.13          | ~ (v1_funct_1 @ X50))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('71', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.89/1.13          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.89/1.13          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.89/1.13          | (zip_tseitin_0 @ sk_D @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['69', '70'])).
% 0.89/1.13  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('74', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.89/1.13          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.89/1.13          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.89/1.13          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.89/1.13  thf('75', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.89/1.13        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['68', '74'])).
% 0.89/1.13  thf(t71_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.13       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.13  thf('76', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.89/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.13  thf('77', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('78', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.89/1.13      inference('demod', [status(thm)], ['76', '77'])).
% 0.89/1.13  thf(d10_xboole_0, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.13  thf('79', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.13  thf('80', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.13      inference('simplify', [status(thm)], ['79'])).
% 0.89/1.13  thf(t79_relat_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ B ) =>
% 0.89/1.13       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.89/1.13         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.89/1.13  thf('81', plain,
% 0.89/1.13      (![X9 : $i, X10 : $i]:
% 0.89/1.13         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.89/1.13          | ((k5_relat_1 @ X9 @ (k6_relat_1 @ X10)) = (X9))
% 0.89/1.13          | ~ (v1_relat_1 @ X9))),
% 0.89/1.13      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.89/1.13  thf('82', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('83', plain,
% 0.89/1.13      (![X9 : $i, X10 : $i]:
% 0.89/1.13         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.89/1.13          | ((k5_relat_1 @ X9 @ (k6_partfun1 @ X10)) = (X9))
% 0.89/1.13          | ~ (v1_relat_1 @ X9))),
% 0.89/1.13      inference('demod', [status(thm)], ['81', '82'])).
% 0.89/1.13  thf('84', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['80', '83'])).
% 0.89/1.13  thf('85', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.89/1.13            = (k6_partfun1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.89/1.13      inference('sup+', [status(thm)], ['78', '84'])).
% 0.89/1.13  thf(fc3_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.89/1.13       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.89/1.13  thf('86', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.13  thf('87', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('88', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 0.89/1.13      inference('demod', [status(thm)], ['86', '87'])).
% 0.89/1.13  thf('89', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.89/1.13           = (k6_partfun1 @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['85', '88'])).
% 0.89/1.13  thf(t53_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( ?[B:$i]:
% 0.89/1.13           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.89/1.13             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.89/1.13         ( v2_funct_1 @ A ) ) ))).
% 0.89/1.13  thf('90', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_funct_1 @ X13)
% 0.89/1.13          | ((k5_relat_1 @ X14 @ X13) != (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.89/1.13          | (v2_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_relat_1 @ X14))),
% 0.89/1.13      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.89/1.13  thf('91', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('92', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_funct_1 @ X13)
% 0.89/1.13          | ((k5_relat_1 @ X14 @ X13) != (k6_partfun1 @ (k1_relat_1 @ X14)))
% 0.89/1.13          | (v2_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_funct_1 @ X14)
% 0.89/1.13          | ~ (v1_relat_1 @ X14))),
% 0.89/1.13      inference('demod', [status(thm)], ['90', '91'])).
% 0.89/1.13  thf('93', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ X0)
% 0.89/1.13            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.89/1.13          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['89', '92'])).
% 0.89/1.13  thf('94', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.89/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.13  thf('95', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('96', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.89/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.89/1.13  thf('97', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 0.89/1.13      inference('demod', [status(thm)], ['86', '87'])).
% 0.89/1.13  thf('98', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.13  thf('99', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('100', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.89/1.13      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.13  thf('101', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.89/1.13      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.13  thf('102', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 0.89/1.13      inference('demod', [status(thm)], ['86', '87'])).
% 0.89/1.13  thf('103', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.89/1.13          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.89/1.13      inference('demod', [status(thm)], ['93', '96', '97', '100', '101', '102'])).
% 0.89/1.13  thf('104', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['103'])).
% 0.89/1.13  thf('105', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('106', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('109', plain,
% 0.89/1.13      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.89/1.13        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13        | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['75', '104', '105', '106', '107', '108'])).
% 0.89/1.13  thf('110', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['109'])).
% 0.89/1.13  thf('111', plain,
% 0.89/1.13      (![X45 : $i, X46 : $i]:
% 0.89/1.13         (((X45) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X45 @ X46))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.89/1.13  thf('112', plain,
% 0.89/1.13      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['110', '111'])).
% 0.89/1.13  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('114', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.89/1.13  thf('115', plain,
% 0.89/1.13      (![X43 : $i, X44 : $i]:
% 0.89/1.13         ((v2_funct_1 @ X44) | ~ (zip_tseitin_0 @ X44 @ X43))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.89/1.13  thf('116', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.13  thf('117', plain,
% 0.89/1.13      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.89/1.13      inference('demod', [status(thm)], ['67', '116'])).
% 0.89/1.13  thf(t61_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v2_funct_1 @ A ) =>
% 0.89/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.89/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.89/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.89/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('118', plain,
% 0.89/1.13      (![X15 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X15)
% 0.89/1.13          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.89/1.13              = (k6_relat_1 @ (k1_relat_1 @ X15)))
% 0.89/1.13          | ~ (v1_funct_1 @ X15)
% 0.89/1.13          | ~ (v1_relat_1 @ X15))),
% 0.89/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.13  thf('119', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('120', plain,
% 0.89/1.13      (![X15 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X15)
% 0.89/1.13          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X15)))
% 0.89/1.13          | ~ (v1_funct_1 @ X15)
% 0.89/1.13          | ~ (v1_relat_1 @ X15))),
% 0.89/1.13      inference('demod', [status(thm)], ['118', '119'])).
% 0.89/1.13  thf('121', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t35_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.89/1.13         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.89/1.13             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.89/1.13  thf('122', plain,
% 0.89/1.13      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.89/1.13         (((X52) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_funct_1 @ X53)
% 0.89/1.13          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 0.89/1.13          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 0.89/1.13          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 0.89/1.13          | ~ (v2_funct_1 @ X53)
% 0.89/1.13          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.13  thf('123', plain,
% 0.89/1.13      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['121', '122'])).
% 0.89/1.13  thf('124', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.13  thf('125', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('127', plain,
% 0.89/1.13      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.89/1.13  thf('128', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('129', plain,
% 0.89/1.13      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 0.89/1.13  thf('130', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.89/1.13  thf('131', plain,
% 0.89/1.13      ((((sk_A) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['129', '130'])).
% 0.89/1.13  thf('132', plain,
% 0.89/1.13      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['131'])).
% 0.89/1.13  thf('133', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.13  thf('134', plain,
% 0.89/1.13      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['132', '133'])).
% 0.89/1.13  thf('135', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup+', [status(thm)], ['120', '134'])).
% 0.89/1.13  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('137', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('138', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.13  thf('139', plain,
% 0.89/1.13      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.89/1.13  thf('140', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.89/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.89/1.13  thf('141', plain,
% 0.89/1.13      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup+', [status(thm)], ['139', '140'])).
% 0.89/1.13  thf('142', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.89/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.89/1.13  thf('143', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['141', '142'])).
% 0.89/1.13  thf('144', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['117', '143'])).
% 0.89/1.13  thf('145', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('146', plain,
% 0.89/1.13      (![X15 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X15)
% 0.89/1.13          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X15)))
% 0.89/1.13          | ~ (v1_funct_1 @ X15)
% 0.89/1.13          | ~ (v1_relat_1 @ X15))),
% 0.89/1.13      inference('demod', [status(thm)], ['118', '119'])).
% 0.89/1.13  thf('147', plain,
% 0.89/1.13      (![X16 : $i, X17 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X16)
% 0.89/1.13          | ~ (v1_funct_1 @ X16)
% 0.89/1.13          | ((X16) = (k2_funct_1 @ X17))
% 0.89/1.13          | ((k5_relat_1 @ X16 @ X17) != (k6_partfun1 @ (k2_relat_1 @ X17)))
% 0.89/1.13          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.89/1.13          | ~ (v2_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_relat_1 @ X17))),
% 0.89/1.13      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.13  thf('148', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['146', '147'])).
% 0.89/1.13  thf('149', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['148'])).
% 0.89/1.13  thf('150', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.89/1.13          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.89/1.13        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['145', '149'])).
% 0.89/1.13  thf('151', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['141', '142'])).
% 0.89/1.13  thf('152', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['57', '58'])).
% 0.89/1.13  thf('153', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('154', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('155', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.13  thf('156', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('demod', [status(thm)], ['63', '64'])).
% 0.89/1.13  thf('158', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('160', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('162', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 0.89/1.13  thf('163', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('164', plain,
% 0.89/1.13      (![X15 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X15)
% 0.89/1.13          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X15)))
% 0.89/1.13          | ~ (v1_funct_1 @ X15)
% 0.89/1.13          | ~ (v1_relat_1 @ X15))),
% 0.89/1.13      inference('demod', [status(thm)], ['118', '119'])).
% 0.89/1.13  thf('165', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('166', plain,
% 0.89/1.13      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.89/1.13         (((X52) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_funct_1 @ X53)
% 0.89/1.13          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 0.89/1.13          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 0.89/1.13          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 0.89/1.13          | ~ (v2_funct_1 @ X53)
% 0.89/1.13          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.13  thf('167', plain,
% 0.89/1.13      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['165', '166'])).
% 0.89/1.13  thf('168', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('170', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('172', plain,
% 0.89/1.13      ((((sk_B) != (sk_B))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.13      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.89/1.13  thf('173', plain,
% 0.89/1.13      ((((sk_B) = (k1_xboole_0))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['172'])).
% 0.89/1.13  thf('174', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('175', plain,
% 0.89/1.13      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 0.89/1.13  thf('176', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['164', '175'])).
% 0.89/1.13  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('demod', [status(thm)], ['63', '64'])).
% 0.89/1.13  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('180', plain,
% 0.89/1.13      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 0.89/1.13  thf('181', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.89/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.89/1.13  thf('182', plain,
% 0.89/1.13      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['180', '181'])).
% 0.89/1.13  thf('183', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.89/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.89/1.13  thf('184', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['182', '183'])).
% 0.89/1.13  thf('185', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.89/1.13  thf('186', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.89/1.13        | ((sk_A) != (sk_A))
% 0.89/1.13        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['150', '151', '152', '153', '154', '155', '156', '157', 
% 0.89/1.13                 '158', '159', '160', '161', '162', '163', '184', '185'])).
% 0.89/1.13  thf('187', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['186'])).
% 0.89/1.13  thf('188', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('189', plain, ($false),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['187', '188'])).
% 0.89/1.13  
% 0.89/1.13  % SZS output end Refutation
% 0.89/1.13  
% 0.89/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
