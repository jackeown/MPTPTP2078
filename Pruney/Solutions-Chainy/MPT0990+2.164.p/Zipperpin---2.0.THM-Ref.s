%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0DS9t19z8F

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:23 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  182 (2166 expanded)
%              Number of leaves         :   45 ( 669 expanded)
%              Depth                    :   18
%              Number of atoms          : 1711 (53167 expanded)
%              Number of equality atoms :  121 (3573 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
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

thf('27',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
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
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','48','53','54','59','73','74','79'])).

thf('81',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

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

thf('83',plain,(
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

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('85',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('86',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','87','88','89','90','91','92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('98',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
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
    inference(demod,[status(thm)],['26','27'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
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
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
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
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('109',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('111',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','41','44','45','46','47'])).

thf('116',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','126','129'])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('132',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109','110','111','112','113','114','115','116','130','131'])).

thf('133',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0DS9t19z8F
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.76/1.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.76/1.97  % Solved by: fo/fo7.sh
% 1.76/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.97  % done 521 iterations in 1.512s
% 1.76/1.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.76/1.97  % SZS output start Refutation
% 1.76/1.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.76/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.97  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.76/1.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.76/1.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.76/1.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.76/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/1.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.76/1.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.76/1.97  thf(sk_D_type, type, sk_D: $i).
% 1.76/1.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.76/1.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.76/1.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.76/1.97  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.76/1.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.76/1.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.76/1.97  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.76/1.97  thf(sk_C_type, type, sk_C: $i).
% 1.76/1.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.76/1.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.76/1.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.76/1.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.76/1.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.76/1.97  thf(t36_funct_2, conjecture,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.76/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.97       ( ![D:$i]:
% 1.76/1.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.76/1.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.76/1.97           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.76/1.97               ( r2_relset_1 @
% 1.76/1.97                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.76/1.97                 ( k6_partfun1 @ A ) ) & 
% 1.76/1.97               ( v2_funct_1 @ C ) ) =>
% 1.76/1.97             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.76/1.97               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.76/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.97    (~( ![A:$i,B:$i,C:$i]:
% 1.76/1.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.76/1.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.97          ( ![D:$i]:
% 1.76/1.97            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.76/1.97                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.76/1.97              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.76/1.97                  ( r2_relset_1 @
% 1.76/1.97                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.76/1.97                    ( k6_partfun1 @ A ) ) & 
% 1.76/1.97                  ( v2_funct_1 @ C ) ) =>
% 1.76/1.97                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.76/1.97                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.76/1.97    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.76/1.97  thf('0', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('1', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(redefinition_k1_partfun1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.76/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.76/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.76/1.97         ( v1_funct_1 @ F ) & 
% 1.76/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.76/1.97       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.76/1.97  thf('2', plain,
% 1.76/1.97      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.76/1.97          | ~ (v1_funct_1 @ X35)
% 1.76/1.97          | ~ (v1_funct_1 @ X38)
% 1.76/1.97          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.76/1.97          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 1.76/1.97              = (k5_relat_1 @ X35 @ X38)))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.76/1.97  thf('3', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.76/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.76/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.76/1.97          | ~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['1', '2'])).
% 1.76/1.97  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('5', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.76/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.76/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.76/1.97          | ~ (v1_funct_1 @ X0))),
% 1.76/1.97      inference('demod', [status(thm)], ['3', '4'])).
% 1.76/1.97  thf('6', plain,
% 1.76/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.76/1.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.76/1.97            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.76/1.97      inference('sup-', [status(thm)], ['0', '5'])).
% 1.76/1.97  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('8', plain,
% 1.76/1.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.76/1.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.76/1.97        (k6_partfun1 @ sk_A))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('9', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('10', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(dt_k1_partfun1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.76/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.76/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.76/1.97         ( v1_funct_1 @ F ) & 
% 1.76/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.76/1.97       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.76/1.97         ( m1_subset_1 @
% 1.76/1.97           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.76/1.97           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.76/1.97  thf('11', plain,
% 1.76/1.97      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.76/1.97          | ~ (v1_funct_1 @ X29)
% 1.76/1.97          | ~ (v1_funct_1 @ X32)
% 1.76/1.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.76/1.97          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 1.76/1.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 1.76/1.97      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.76/1.97  thf('12', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.76/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.76/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.76/1.97          | ~ (v1_funct_1 @ X1)
% 1.76/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.76/1.97  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('14', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.76/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.76/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.76/1.97          | ~ (v1_funct_1 @ X1))),
% 1.76/1.97      inference('demod', [status(thm)], ['12', '13'])).
% 1.76/1.97  thf('15', plain,
% 1.76/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.76/1.97        | (m1_subset_1 @ 
% 1.76/1.97           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.76/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.76/1.97      inference('sup-', [status(thm)], ['9', '14'])).
% 1.76/1.97  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('17', plain,
% 1.76/1.97      ((m1_subset_1 @ 
% 1.76/1.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.76/1.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.76/1.97      inference('demod', [status(thm)], ['15', '16'])).
% 1.76/1.97  thf(redefinition_r2_relset_1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.97     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.76/1.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.97       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.76/1.97  thf('18', plain,
% 1.76/1.97      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.76/1.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.76/1.97          | ((X16) = (X19))
% 1.76/1.97          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.76/1.97  thf('19', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.76/1.97             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.76/1.97          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.76/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.76/1.97      inference('sup-', [status(thm)], ['17', '18'])).
% 1.76/1.97  thf('20', plain,
% 1.76/1.97      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.76/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.76/1.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.76/1.97            = (k6_partfun1 @ sk_A)))),
% 1.76/1.97      inference('sup-', [status(thm)], ['8', '19'])).
% 1.76/1.97  thf(t29_relset_1, axiom,
% 1.76/1.97    (![A:$i]:
% 1.76/1.97     ( m1_subset_1 @
% 1.76/1.97       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.76/1.97  thf('21', plain,
% 1.76/1.97      (![X20 : $i]:
% 1.76/1.97         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.76/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.76/1.97  thf(redefinition_k6_partfun1, axiom,
% 1.76/1.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.76/1.97  thf('22', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.76/1.97  thf('23', plain,
% 1.76/1.97      (![X20 : $i]:
% 1.76/1.97         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 1.76/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.76/1.97      inference('demod', [status(thm)], ['21', '22'])).
% 1.76/1.97  thf('24', plain,
% 1.76/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.76/1.97         = (k6_partfun1 @ sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['20', '23'])).
% 1.76/1.97  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.76/1.97  thf(t64_funct_1, axiom,
% 1.76/1.97    (![A:$i]:
% 1.76/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.76/1.97       ( ![B:$i]:
% 1.76/1.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.76/1.97           ( ( ( v2_funct_1 @ A ) & 
% 1.76/1.97               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.76/1.97               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.76/1.97             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.76/1.97  thf('26', plain,
% 1.76/1.97      (![X8 : $i, X9 : $i]:
% 1.76/1.97         (~ (v1_relat_1 @ X8)
% 1.76/1.97          | ~ (v1_funct_1 @ X8)
% 1.76/1.97          | ((X8) = (k2_funct_1 @ X9))
% 1.76/1.97          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 1.76/1.97          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.76/1.97          | ~ (v2_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_relat_1 @ X9))),
% 1.76/1.97      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.76/1.97  thf('27', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.76/1.97  thf('28', plain,
% 1.76/1.97      (![X8 : $i, X9 : $i]:
% 1.76/1.97         (~ (v1_relat_1 @ X8)
% 1.76/1.97          | ~ (v1_funct_1 @ X8)
% 1.76/1.97          | ((X8) = (k2_funct_1 @ X9))
% 1.76/1.97          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 1.76/1.97          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.76/1.97          | ~ (v2_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_relat_1 @ X9))),
% 1.76/1.97      inference('demod', [status(thm)], ['26', '27'])).
% 1.76/1.97  thf('29', plain,
% 1.76/1.97      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.76/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.76/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.76/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.76/1.97        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.76/1.97        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.76/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.76/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['25', '28'])).
% 1.76/1.97  thf('30', plain,
% 1.76/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.76/1.97         = (k6_partfun1 @ sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['20', '23'])).
% 1.76/1.97  thf('31', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(t24_funct_2, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.76/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.97       ( ![D:$i]:
% 1.76/1.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.76/1.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.76/1.97           ( ( r2_relset_1 @
% 1.76/1.97               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.76/1.97               ( k6_partfun1 @ B ) ) =>
% 1.76/1.97             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.76/1.97  thf('32', plain,
% 1.76/1.97      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.76/1.97         (~ (v1_funct_1 @ X42)
% 1.76/1.97          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 1.76/1.97          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.76/1.97          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 1.76/1.97               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 1.76/1.97               (k6_partfun1 @ X43))
% 1.76/1.97          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 1.76/1.97          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 1.76/1.97          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 1.76/1.97          | ~ (v1_funct_1 @ X45))),
% 1.76/1.97      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.76/1.97  thf('33', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.76/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.76/1.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.76/1.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.76/1.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.76/1.97               (k6_partfun1 @ sk_A))
% 1.76/1.97          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.76/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['31', '32'])).
% 1.76/1.97  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('36', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.76/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.76/1.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.76/1.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.76/1.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.76/1.97               (k6_partfun1 @ sk_A)))),
% 1.76/1.97      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.76/1.97  thf('37', plain,
% 1.76/1.97      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.76/1.97           (k6_partfun1 @ sk_A))
% 1.76/1.97        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.76/1.97        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.76/1.97        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.76/1.97        | ~ (v1_funct_1 @ sk_D))),
% 1.76/1.97      inference('sup-', [status(thm)], ['30', '36'])).
% 1.76/1.97  thf('38', plain,
% 1.76/1.97      (![X20 : $i]:
% 1.76/1.97         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 1.76/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.76/1.97      inference('demod', [status(thm)], ['21', '22'])).
% 1.76/1.97  thf('39', plain,
% 1.76/1.97      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.76/1.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.76/1.97          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 1.76/1.97          | ((X16) != (X19)))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.76/1.97  thf('40', plain,
% 1.76/1.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.97         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 1.76/1.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.76/1.97      inference('simplify', [status(thm)], ['39'])).
% 1.76/1.97  thf('41', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.76/1.97      inference('sup-', [status(thm)], ['38', '40'])).
% 1.76/1.97  thf('42', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(redefinition_k2_relset_1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.76/1.97  thf('43', plain,
% 1.76/1.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.76/1.97         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.76/1.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.76/1.97  thf('44', plain,
% 1.76/1.97      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.76/1.97      inference('sup-', [status(thm)], ['42', '43'])).
% 1.76/1.97  thf('45', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 1.76/1.97  thf('49', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(cc2_relat_1, axiom,
% 1.76/1.97    (![A:$i]:
% 1.76/1.97     ( ( v1_relat_1 @ A ) =>
% 1.76/1.97       ( ![B:$i]:
% 1.76/1.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.76/1.97  thf('50', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.76/1.97          | (v1_relat_1 @ X0)
% 1.76/1.97          | ~ (v1_relat_1 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.76/1.97  thf('51', plain,
% 1.76/1.97      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.76/1.97      inference('sup-', [status(thm)], ['49', '50'])).
% 1.76/1.97  thf(fc6_relat_1, axiom,
% 1.76/1.97    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.76/1.97  thf('52', plain,
% 1.76/1.97      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.76/1.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.76/1.97  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 1.76/1.97      inference('demod', [status(thm)], ['51', '52'])).
% 1.76/1.97  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('55', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('56', plain,
% 1.76/1.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.76/1.97         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.76/1.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.76/1.97  thf('57', plain,
% 1.76/1.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/1.97  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.76/1.97      inference('sup+', [status(thm)], ['57', '58'])).
% 1.76/1.97  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(d1_funct_2, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.97       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.76/1.97           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.76/1.97             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.76/1.97         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.97           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.76/1.97             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.76/1.97  thf(zf_stmt_1, axiom,
% 1.76/1.97    (![C:$i,B:$i,A:$i]:
% 1.76/1.97     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.76/1.97       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.76/1.97  thf('61', plain,
% 1.76/1.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.76/1.97         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.76/1.97          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.76/1.97          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/1.97  thf('62', plain,
% 1.76/1.97      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.76/1.97        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.76/1.97      inference('sup-', [status(thm)], ['60', '61'])).
% 1.76/1.97  thf(zf_stmt_2, axiom,
% 1.76/1.97    (![B:$i,A:$i]:
% 1.76/1.97     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.97       ( zip_tseitin_0 @ B @ A ) ))).
% 1.76/1.97  thf('63', plain,
% 1.76/1.97      (![X21 : $i, X22 : $i]:
% 1.76/1.97         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.76/1.97  thf('64', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.76/1.97  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.76/1.97  thf(zf_stmt_5, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.97       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.76/1.97         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.76/1.97           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.76/1.97             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.76/1.97  thf('65', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.76/1.97         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.76/1.97          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.76/1.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.76/1.97  thf('66', plain,
% 1.76/1.97      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.76/1.97      inference('sup-', [status(thm)], ['64', '65'])).
% 1.76/1.97  thf('67', plain,
% 1.76/1.97      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.76/1.97      inference('sup-', [status(thm)], ['63', '66'])).
% 1.76/1.97  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.76/1.97      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.76/1.97  thf('70', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(redefinition_k1_relset_1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.76/1.97       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.76/1.97  thf('71', plain,
% 1.76/1.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.76/1.97         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.76/1.97          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.76/1.97  thf('72', plain,
% 1.76/1.97      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.76/1.97      inference('sup-', [status(thm)], ['70', '71'])).
% 1.76/1.97  thf('73', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.76/1.97  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('75', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('76', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.76/1.97          | (v1_relat_1 @ X0)
% 1.76/1.97          | ~ (v1_relat_1 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.76/1.97  thf('77', plain,
% 1.76/1.97      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['75', '76'])).
% 1.76/1.97  thf('78', plain,
% 1.76/1.97      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.76/1.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.76/1.97  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.97      inference('demod', [status(thm)], ['77', '78'])).
% 1.76/1.97  thf('80', plain,
% 1.76/1.97      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.76/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.76/1.97        | ((sk_B) != (sk_B))
% 1.76/1.97        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.76/1.97      inference('demod', [status(thm)],
% 1.76/1.97                ['29', '48', '53', '54', '59', '73', '74', '79'])).
% 1.76/1.97  thf('81', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.76/1.97      inference('simplify', [status(thm)], ['80'])).
% 1.76/1.97  thf('82', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.76/1.97  thf(t48_funct_1, axiom,
% 1.76/1.97    (![A:$i]:
% 1.76/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.76/1.97       ( ![B:$i]:
% 1.76/1.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.76/1.97           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.76/1.97               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.76/1.97             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.76/1.97  thf('83', plain,
% 1.76/1.97      (![X4 : $i, X5 : $i]:
% 1.76/1.97         (~ (v1_relat_1 @ X4)
% 1.76/1.97          | ~ (v1_funct_1 @ X4)
% 1.76/1.97          | (v2_funct_1 @ X5)
% 1.76/1.97          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 1.76/1.97          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 1.76/1.97          | ~ (v1_funct_1 @ X5)
% 1.76/1.97          | ~ (v1_relat_1 @ X5))),
% 1.76/1.97      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.76/1.97  thf('84', plain,
% 1.76/1.97      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.76/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.76/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.76/1.97        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.76/1.97        | (v2_funct_1 @ sk_D)
% 1.76/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.76/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['82', '83'])).
% 1.76/1.97  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.76/1.97  thf('85', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.76/1.97      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.76/1.97  thf('86', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.76/1.97  thf('87', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 1.76/1.97      inference('demod', [status(thm)], ['85', '86'])).
% 1.76/1.97  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.76/1.97      inference('demod', [status(thm)], ['51', '52'])).
% 1.76/1.97  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.76/1.97      inference('sup+', [status(thm)], ['57', '58'])).
% 1.76/1.97  thf('91', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.76/1.97  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.97      inference('demod', [status(thm)], ['77', '78'])).
% 1.76/1.97  thf('94', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)],
% 1.76/1.97                ['84', '87', '88', '89', '90', '91', '92', '93'])).
% 1.76/1.97  thf('95', plain, ((v2_funct_1 @ sk_D)),
% 1.76/1.97      inference('simplify', [status(thm)], ['94'])).
% 1.76/1.97  thf('96', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf(t61_funct_1, axiom,
% 1.76/1.97    (![A:$i]:
% 1.76/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.76/1.97       ( ( v2_funct_1 @ A ) =>
% 1.76/1.97         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.76/1.97             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.76/1.97           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.76/1.97             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.76/1.97  thf('97', plain,
% 1.76/1.97      (![X7 : $i]:
% 1.76/1.97         (~ (v2_funct_1 @ X7)
% 1.76/1.97          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 1.76/1.97              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 1.76/1.97          | ~ (v1_funct_1 @ X7)
% 1.76/1.97          | ~ (v1_relat_1 @ X7))),
% 1.76/1.97      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.76/1.97  thf('98', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.76/1.97  thf('99', plain,
% 1.76/1.97      (![X7 : $i]:
% 1.76/1.97         (~ (v2_funct_1 @ X7)
% 1.76/1.97          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 1.76/1.97              = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 1.76/1.97          | ~ (v1_funct_1 @ X7)
% 1.76/1.97          | ~ (v1_relat_1 @ X7))),
% 1.76/1.97      inference('demod', [status(thm)], ['97', '98'])).
% 1.76/1.97  thf('100', plain,
% 1.76/1.97      (![X8 : $i, X9 : $i]:
% 1.76/1.97         (~ (v1_relat_1 @ X8)
% 1.76/1.97          | ~ (v1_funct_1 @ X8)
% 1.76/1.97          | ((X8) = (k2_funct_1 @ X9))
% 1.76/1.97          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 1.76/1.97          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 1.76/1.97          | ~ (v2_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_funct_1 @ X9)
% 1.76/1.97          | ~ (v1_relat_1 @ X9))),
% 1.76/1.97      inference('demod', [status(thm)], ['26', '27'])).
% 1.76/1.97  thf('101', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.76/1.97            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.76/1.97          | ~ (v1_relat_1 @ X0)
% 1.76/1.97          | ~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v2_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.76/1.97          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.76/1.97          | ~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_relat_1 @ X0))),
% 1.76/1.97      inference('sup-', [status(thm)], ['99', '100'])).
% 1.76/1.97  thf('102', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.76/1.97          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.76/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.76/1.97          | ~ (v2_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_funct_1 @ X0)
% 1.76/1.97          | ~ (v1_relat_1 @ X0)
% 1.76/1.97          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.76/1.97              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.76/1.97      inference('simplify', [status(thm)], ['101'])).
% 1.76/1.97  thf('103', plain,
% 1.76/1.97      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 1.76/1.97          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.76/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.76/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.76/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.76/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.76/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.76/1.97        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.76/1.97        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.76/1.97        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.76/1.97      inference('sup-', [status(thm)], ['96', '102'])).
% 1.76/1.97  thf('104', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.76/1.97  thf('105', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.76/1.97      inference('sup+', [status(thm)], ['57', '58'])).
% 1.76/1.97  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 1.76/1.97      inference('demod', [status(thm)], ['51', '52'])).
% 1.76/1.97  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('108', plain, ((v2_funct_1 @ sk_D)),
% 1.76/1.97      inference('simplify', [status(thm)], ['94'])).
% 1.76/1.97  thf('109', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.76/1.97      inference('demod', [status(thm)], ['77', '78'])).
% 1.76/1.97  thf('111', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('113', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('115', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['37', '41', '44', '45', '46', '47'])).
% 1.76/1.97  thf('116', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('118', plain,
% 1.76/1.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.76/1.97         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.76/1.97          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.76/1.97          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/1.97  thf('119', plain,
% 1.76/1.97      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.76/1.97        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.97      inference('sup-', [status(thm)], ['117', '118'])).
% 1.76/1.97  thf('120', plain,
% 1.76/1.97      (![X21 : $i, X22 : $i]:
% 1.76/1.97         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.76/1.97  thf('121', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('122', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.76/1.97         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.76/1.97          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.76/1.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.76/1.97  thf('123', plain,
% 1.76/1.97      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.76/1.97      inference('sup-', [status(thm)], ['121', '122'])).
% 1.76/1.97  thf('124', plain,
% 1.76/1.97      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.76/1.97      inference('sup-', [status(thm)], ['120', '123'])).
% 1.76/1.97  thf('125', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('126', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.76/1.97      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 1.76/1.97  thf('127', plain,
% 1.76/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('128', plain,
% 1.76/1.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.76/1.97         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.76/1.97          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.76/1.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.76/1.97  thf('129', plain,
% 1.76/1.97      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.76/1.97      inference('sup-', [status(thm)], ['127', '128'])).
% 1.76/1.97  thf('130', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.76/1.97      inference('demod', [status(thm)], ['119', '126', '129'])).
% 1.76/1.97  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.76/1.97      inference('demod', [status(thm)], ['81', '95'])).
% 1.76/1.97  thf('132', plain,
% 1.76/1.97      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.76/1.97        | ((sk_A) != (sk_A))
% 1.76/1.97        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.76/1.97      inference('demod', [status(thm)],
% 1.76/1.97                ['103', '104', '105', '106', '107', '108', '109', '110', 
% 1.76/1.97                 '111', '112', '113', '114', '115', '116', '130', '131'])).
% 1.76/1.97  thf('133', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.76/1.97      inference('simplify', [status(thm)], ['132'])).
% 1.76/1.97  thf('134', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('135', plain, ($false),
% 1.76/1.97      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 1.76/1.97  
% 1.76/1.97  % SZS output end Refutation
% 1.76/1.97  
% 1.76/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
