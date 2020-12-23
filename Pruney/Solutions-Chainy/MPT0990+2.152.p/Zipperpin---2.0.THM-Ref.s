%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrc3psrZXB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:21 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 771 expanded)
%              Number of leaves         :   51 ( 254 expanded)
%              Depth                    :   19
%              Number of atoms          : 1542 (18084 expanded)
%              Number of equality atoms :   96 (1177 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
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

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','26'])).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( r2_relset_1 @ X50 @ X50 @ ( k1_partfun1 @ X50 @ X51 @ X51 @ X50 @ X49 @ X52 ) @ ( k6_partfun1 @ X50 ) )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
        = X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('33',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( r2_relset_1 @ X50 @ X50 @ ( k1_partfun1 @ X50 @ X51 @ X51 @ X50 @ X49 @ X52 ) @ ( k6_relat_1 @ X50 ) )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
        = X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','43','46','47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','43','46','47','48','49'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('64',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_relset_1 @ X23 @ X24 @ X25 @ X24 )
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('67',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['67','70','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('84',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','50','55','56','61','84','85','90'])).

thf('92',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','26'])).

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

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('95',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['59','60'])).

thf('100',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','82','83'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('103',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102'])).

thf('104',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','104'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('106',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('107',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('109',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['103'])).

thf('111',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrc3psrZXB
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.72/1.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.96  % Solved by: fo/fo7.sh
% 1.72/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.96  % done 461 iterations in 1.487s
% 1.72/1.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.96  % SZS output start Refutation
% 1.72/1.96  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.72/1.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.96  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.72/1.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.72/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.72/1.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.72/1.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.72/1.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.72/1.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.72/1.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.72/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.96  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.72/1.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.72/1.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.72/1.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.72/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.96  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.72/1.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.72/1.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.72/1.96  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.72/1.96  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.72/1.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.72/1.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.72/1.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.72/1.96  thf(sk_D_type, type, sk_D: $i).
% 1.72/1.96  thf(t36_funct_2, conjecture,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.96       ( ![D:$i]:
% 1.72/1.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.96           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.96               ( r2_relset_1 @
% 1.72/1.96                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.96                 ( k6_partfun1 @ A ) ) & 
% 1.72/1.96               ( v2_funct_1 @ C ) ) =>
% 1.72/1.96             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.96               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.72/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.96    (~( ![A:$i,B:$i,C:$i]:
% 1.72/1.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.96          ( ![D:$i]:
% 1.72/1.96            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.96                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.96              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.72/1.96                  ( r2_relset_1 @
% 1.72/1.96                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.72/1.96                    ( k6_partfun1 @ A ) ) & 
% 1.72/1.96                  ( v2_funct_1 @ C ) ) =>
% 1.72/1.96                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.96                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.72/1.96    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.72/1.96  thf('0', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('1', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(redefinition_k1_partfun1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.96     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.96         ( v1_funct_1 @ F ) & 
% 1.72/1.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.72/1.96  thf('2', plain,
% 1.72/1.96      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.72/1.96          | ~ (v1_funct_1 @ X42)
% 1.72/1.96          | ~ (v1_funct_1 @ X45)
% 1.72/1.96          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.72/1.96          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 1.72/1.96              = (k5_relat_1 @ X42 @ X45)))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.72/1.96  thf('3', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.96            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.96          | ~ (v1_funct_1 @ X0)
% 1.72/1.96          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.72/1.96  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('5', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.72/1.96            = (k5_relat_1 @ sk_C @ X0))
% 1.72/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.72/1.96          | ~ (v1_funct_1 @ X0))),
% 1.72/1.96      inference('demod', [status(thm)], ['3', '4'])).
% 1.72/1.96  thf('6', plain,
% 1.72/1.96      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.96            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.72/1.96      inference('sup-', [status(thm)], ['0', '5'])).
% 1.72/1.96  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('8', plain,
% 1.72/1.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.96        (k6_partfun1 @ sk_A))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(redefinition_k6_partfun1, axiom,
% 1.72/1.96    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.72/1.96  thf('9', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.96  thf('10', plain,
% 1.72/1.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.96        (k6_relat_1 @ sk_A))),
% 1.72/1.96      inference('demod', [status(thm)], ['8', '9'])).
% 1.72/1.96  thf('11', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('12', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(dt_k1_partfun1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.72/1.96     ( ( ( v1_funct_1 @ E ) & 
% 1.72/1.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.96         ( v1_funct_1 @ F ) & 
% 1.72/1.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.72/1.96       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.72/1.96         ( m1_subset_1 @
% 1.72/1.96           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.72/1.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.72/1.96  thf('13', plain,
% 1.72/1.96      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.72/1.96          | ~ (v1_funct_1 @ X34)
% 1.72/1.96          | ~ (v1_funct_1 @ X37)
% 1.72/1.96          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.72/1.96          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 1.72/1.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 1.72/1.96      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.72/1.96  thf('14', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.96          | ~ (v1_funct_1 @ X1)
% 1.72/1.96          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['12', '13'])).
% 1.72/1.96  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('16', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.72/1.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.72/1.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.72/1.96          | ~ (v1_funct_1 @ X1))),
% 1.72/1.96      inference('demod', [status(thm)], ['14', '15'])).
% 1.72/1.96  thf('17', plain,
% 1.72/1.96      ((~ (v1_funct_1 @ sk_D)
% 1.72/1.96        | (m1_subset_1 @ 
% 1.72/1.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.96      inference('sup-', [status(thm)], ['11', '16'])).
% 1.72/1.96  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('19', plain,
% 1.72/1.96      ((m1_subset_1 @ 
% 1.72/1.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.72/1.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.72/1.96      inference('demod', [status(thm)], ['17', '18'])).
% 1.72/1.96  thf(redefinition_r2_relset_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.72/1.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.72/1.96  thf('20', plain,
% 1.72/1.96      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.72/1.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.72/1.96          | ((X19) = (X22))
% 1.72/1.96          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.72/1.96  thf('21', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.96             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.72/1.96          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.72/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.72/1.96      inference('sup-', [status(thm)], ['19', '20'])).
% 1.72/1.96  thf('22', plain,
% 1.72/1.96      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.72/1.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.72/1.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.96            = (k6_relat_1 @ sk_A)))),
% 1.72/1.96      inference('sup-', [status(thm)], ['10', '21'])).
% 1.72/1.96  thf(dt_k6_partfun1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( m1_subset_1 @
% 1.72/1.96         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.72/1.96       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.72/1.96  thf('23', plain,
% 1.72/1.96      (![X41 : $i]:
% 1.72/1.96         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 1.72/1.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 1.72/1.96      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.72/1.96  thf('24', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.96  thf('25', plain,
% 1.72/1.96      (![X41 : $i]:
% 1.72/1.96         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 1.72/1.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 1.72/1.96      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.96  thf('26', plain,
% 1.72/1.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.96         = (k6_relat_1 @ sk_A))),
% 1.72/1.96      inference('demod', [status(thm)], ['22', '25'])).
% 1.72/1.96  thf('27', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['6', '7', '26'])).
% 1.72/1.96  thf(t64_funct_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.96       ( ![B:$i]:
% 1.72/1.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.72/1.96           ( ( ( v2_funct_1 @ A ) & 
% 1.72/1.96               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.72/1.96               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.72/1.96             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.72/1.96  thf('28', plain,
% 1.72/1.96      (![X9 : $i, X10 : $i]:
% 1.72/1.96         (~ (v1_relat_1 @ X9)
% 1.72/1.96          | ~ (v1_funct_1 @ X9)
% 1.72/1.96          | ((X9) = (k2_funct_1 @ X10))
% 1.72/1.96          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.72/1.96          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.72/1.96          | ~ (v2_funct_1 @ X10)
% 1.72/1.96          | ~ (v1_funct_1 @ X10)
% 1.72/1.96          | ~ (v1_relat_1 @ X10))),
% 1.72/1.96      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.72/1.96  thf('29', plain,
% 1.72/1.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.72/1.96        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.96        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.96        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.96        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.72/1.96        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.72/1.96        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.96        | ~ (v1_relat_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.96  thf('30', plain,
% 1.72/1.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.72/1.96         = (k6_relat_1 @ sk_A))),
% 1.72/1.96      inference('demod', [status(thm)], ['22', '25'])).
% 1.72/1.96  thf('31', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(t24_funct_2, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.72/1.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.72/1.96       ( ![D:$i]:
% 1.72/1.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.72/1.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.72/1.96           ( ( r2_relset_1 @
% 1.72/1.96               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.72/1.96               ( k6_partfun1 @ B ) ) =>
% 1.72/1.96             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.72/1.96  thf('32', plain,
% 1.72/1.96      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.96         (~ (v1_funct_1 @ X49)
% 1.72/1.96          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 1.72/1.96          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.72/1.96          | ~ (r2_relset_1 @ X50 @ X50 @ 
% 1.72/1.96               (k1_partfun1 @ X50 @ X51 @ X51 @ X50 @ X49 @ X52) @ 
% 1.72/1.96               (k6_partfun1 @ X50))
% 1.72/1.96          | ((k2_relset_1 @ X51 @ X50 @ X52) = (X50))
% 1.72/1.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 1.72/1.96          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 1.72/1.96          | ~ (v1_funct_1 @ X52))),
% 1.72/1.96      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.72/1.96  thf('33', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.72/1.96  thf('34', plain,
% 1.72/1.96      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.96         (~ (v1_funct_1 @ X49)
% 1.72/1.96          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 1.72/1.96          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.72/1.96          | ~ (r2_relset_1 @ X50 @ X50 @ 
% 1.72/1.96               (k1_partfun1 @ X50 @ X51 @ X51 @ X50 @ X49 @ X52) @ 
% 1.72/1.96               (k6_relat_1 @ X50))
% 1.72/1.96          | ((k2_relset_1 @ X51 @ X50 @ X52) = (X50))
% 1.72/1.96          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 1.72/1.96          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 1.72/1.96          | ~ (v1_funct_1 @ X52))),
% 1.72/1.96      inference('demod', [status(thm)], ['32', '33'])).
% 1.72/1.96  thf('35', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (~ (v1_funct_1 @ X0)
% 1.72/1.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.96               (k6_relat_1 @ sk_A))
% 1.72/1.96          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.72/1.96          | ~ (v1_funct_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['31', '34'])).
% 1.72/1.96  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('38', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (~ (v1_funct_1 @ X0)
% 1.72/1.96          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.72/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.96          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.72/1.96          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.72/1.96               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.72/1.96               (k6_relat_1 @ sk_A)))),
% 1.72/1.96      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.72/1.96  thf('39', plain,
% 1.72/1.96      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.72/1.96           (k6_relat_1 @ sk_A))
% 1.72/1.96        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.72/1.96        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.72/1.96        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.72/1.96        | ~ (v1_funct_1 @ sk_D))),
% 1.72/1.96      inference('sup-', [status(thm)], ['30', '38'])).
% 1.72/1.96  thf('40', plain,
% 1.72/1.96      (![X41 : $i]:
% 1.72/1.96         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 1.72/1.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 1.72/1.96      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.96  thf('41', plain,
% 1.72/1.96      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.72/1.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.72/1.96          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 1.72/1.96          | ((X19) != (X22)))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.72/1.96  thf('42', plain,
% 1.72/1.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.72/1.96         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.72/1.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.72/1.96      inference('simplify', [status(thm)], ['41'])).
% 1.72/1.96  thf('43', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.72/1.96      inference('sup-', [status(thm)], ['40', '42'])).
% 1.72/1.96  thf('44', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(redefinition_k2_relset_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.72/1.96  thf('45', plain,
% 1.72/1.96      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.72/1.96         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.72/1.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.72/1.96  thf('46', plain,
% 1.72/1.96      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.72/1.96      inference('sup-', [status(thm)], ['44', '45'])).
% 1.72/1.96  thf('47', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('50', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.72/1.96      inference('demod', [status(thm)], ['39', '43', '46', '47', '48', '49'])).
% 1.72/1.96  thf('51', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(cc2_relat_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( v1_relat_1 @ A ) =>
% 1.72/1.96       ( ![B:$i]:
% 1.72/1.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.72/1.96  thf('52', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.72/1.96          | (v1_relat_1 @ X0)
% 1.72/1.96          | ~ (v1_relat_1 @ X1))),
% 1.72/1.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.72/1.96  thf('53', plain,
% 1.72/1.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.72/1.96      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.96  thf(fc6_relat_1, axiom,
% 1.72/1.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.72/1.96  thf('54', plain,
% 1.72/1.96      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.72/1.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.72/1.96  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.96      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.96  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('57', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('58', plain,
% 1.72/1.96      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.72/1.96         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.72/1.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.72/1.96  thf('59', plain,
% 1.72/1.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['57', '58'])).
% 1.72/1.96  thf('60', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('61', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.96      inference('sup+', [status(thm)], ['59', '60'])).
% 1.72/1.96  thf('62', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.72/1.96      inference('demod', [status(thm)], ['39', '43', '46', '47', '48', '49'])).
% 1.72/1.96  thf(t169_relat_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( v1_relat_1 @ A ) =>
% 1.72/1.96       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.72/1.96  thf('63', plain,
% 1.72/1.96      (![X4 : $i]:
% 1.72/1.96         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 1.72/1.96          | ~ (v1_relat_1 @ X4))),
% 1.72/1.96      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.72/1.96  thf('64', plain,
% 1.72/1.96      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 1.72/1.96        | ~ (v1_relat_1 @ sk_D))),
% 1.72/1.96      inference('sup+', [status(thm)], ['62', '63'])).
% 1.72/1.96  thf('65', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(t38_relset_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.96       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.72/1.96         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.72/1.96  thf('66', plain,
% 1.72/1.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.96         (((k8_relset_1 @ X23 @ X24 @ X25 @ X24)
% 1.72/1.96            = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.72/1.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.72/1.96      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.72/1.96  thf('67', plain,
% 1.72/1.96      (((k8_relset_1 @ sk_B @ sk_A @ sk_D @ sk_A)
% 1.72/1.96         = (k1_relset_1 @ sk_B @ sk_A @ sk_D))),
% 1.72/1.96      inference('sup-', [status(thm)], ['65', '66'])).
% 1.72/1.96  thf('68', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(redefinition_k8_relset_1, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.96       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.72/1.96  thf('69', plain,
% 1.72/1.96      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.72/1.96          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 1.72/1.96      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.72/1.96  thf('70', plain,
% 1.72/1.96      (![X0 : $i]:
% 1.72/1.96         ((k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 1.72/1.96      inference('sup-', [status(thm)], ['68', '69'])).
% 1.72/1.96  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(d1_funct_2, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.72/1.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.72/1.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.72/1.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.72/1.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.72/1.96  thf(zf_stmt_1, axiom,
% 1.72/1.96    (![C:$i,B:$i,A:$i]:
% 1.72/1.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.72/1.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.72/1.96  thf('72', plain,
% 1.72/1.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.72/1.96         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 1.72/1.96          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 1.72/1.96          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.72/1.96  thf('73', plain,
% 1.72/1.96      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.72/1.96        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.72/1.96      inference('sup-', [status(thm)], ['71', '72'])).
% 1.72/1.96  thf(zf_stmt_2, axiom,
% 1.72/1.96    (![B:$i,A:$i]:
% 1.72/1.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.72/1.96       ( zip_tseitin_0 @ B @ A ) ))).
% 1.72/1.96  thf('74', plain,
% 1.72/1.96      (![X26 : $i, X27 : $i]:
% 1.72/1.96         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.72/1.96  thf('75', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.72/1.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.72/1.96  thf(zf_stmt_5, axiom,
% 1.72/1.96    (![A:$i,B:$i,C:$i]:
% 1.72/1.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.72/1.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.72/1.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.72/1.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.72/1.96  thf('76', plain,
% 1.72/1.96      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.72/1.96         (~ (zip_tseitin_0 @ X31 @ X32)
% 1.72/1.96          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 1.72/1.96          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.72/1.96  thf('77', plain,
% 1.72/1.96      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.72/1.96      inference('sup-', [status(thm)], ['75', '76'])).
% 1.72/1.96  thf('78', plain,
% 1.72/1.96      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.72/1.96      inference('sup-', [status(thm)], ['74', '77'])).
% 1.72/1.96  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('80', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.72/1.96      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 1.72/1.96  thf('81', plain, (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['73', '80'])).
% 1.72/1.96  thf('82', plain, (((k10_relat_1 @ sk_D @ sk_A) = (sk_B))),
% 1.72/1.96      inference('demod', [status(thm)], ['67', '70', '81'])).
% 1.72/1.96  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.96      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.96  thf('84', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['64', '82', '83'])).
% 1.72/1.96  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('86', plain,
% 1.72/1.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('87', plain,
% 1.72/1.96      (![X0 : $i, X1 : $i]:
% 1.72/1.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.72/1.96          | (v1_relat_1 @ X0)
% 1.72/1.96          | ~ (v1_relat_1 @ X1))),
% 1.72/1.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.72/1.96  thf('88', plain,
% 1.72/1.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['86', '87'])).
% 1.72/1.96  thf('89', plain,
% 1.72/1.96      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.72/1.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.72/1.96  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.96      inference('demod', [status(thm)], ['88', '89'])).
% 1.72/1.96  thf('91', plain,
% 1.72/1.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.72/1.96        | ~ (v2_funct_1 @ sk_D)
% 1.72/1.96        | ((sk_B) != (sk_B))
% 1.72/1.96        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.72/1.96      inference('demod', [status(thm)],
% 1.72/1.96                ['29', '50', '55', '56', '61', '84', '85', '90'])).
% 1.72/1.96  thf('92', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.96      inference('simplify', [status(thm)], ['91'])).
% 1.72/1.96  thf('93', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['6', '7', '26'])).
% 1.72/1.96  thf(t48_funct_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.96       ( ![B:$i]:
% 1.72/1.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.72/1.96           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.72/1.96               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.72/1.96             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.72/1.96  thf('94', plain,
% 1.72/1.96      (![X7 : $i, X8 : $i]:
% 1.72/1.96         (~ (v1_relat_1 @ X7)
% 1.72/1.96          | ~ (v1_funct_1 @ X7)
% 1.72/1.96          | (v2_funct_1 @ X8)
% 1.72/1.96          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.72/1.96          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 1.72/1.96          | ~ (v1_funct_1 @ X8)
% 1.72/1.96          | ~ (v1_relat_1 @ X8))),
% 1.72/1.96      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.72/1.96  thf('95', plain,
% 1.72/1.96      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.72/1.96        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.96        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.96        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.72/1.96        | (v2_funct_1 @ sk_D)
% 1.72/1.96        | ~ (v1_funct_1 @ sk_C)
% 1.72/1.96        | ~ (v1_relat_1 @ sk_C))),
% 1.72/1.96      inference('sup-', [status(thm)], ['93', '94'])).
% 1.72/1.96  thf(fc4_funct_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.72/1.96       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.72/1.96  thf('96', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.72/1.96      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.72/1.96  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.96      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.96  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('99', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.72/1.96      inference('sup+', [status(thm)], ['59', '60'])).
% 1.72/1.96  thf('100', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['64', '82', '83'])).
% 1.72/1.96  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 1.72/1.96      inference('demod', [status(thm)], ['88', '89'])).
% 1.72/1.96  thf('103', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)],
% 1.72/1.96                ['95', '96', '97', '98', '99', '100', '101', '102'])).
% 1.72/1.96  thf('104', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.96      inference('simplify', [status(thm)], ['103'])).
% 1.72/1.96  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['92', '104'])).
% 1.72/1.96  thf(t65_funct_1, axiom,
% 1.72/1.96    (![A:$i]:
% 1.72/1.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.72/1.96       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.72/1.96  thf('106', plain,
% 1.72/1.96      (![X11 : $i]:
% 1.72/1.96         (~ (v2_funct_1 @ X11)
% 1.72/1.96          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 1.72/1.96          | ~ (v1_funct_1 @ X11)
% 1.72/1.96          | ~ (v1_relat_1 @ X11))),
% 1.72/1.96      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.72/1.96  thf('107', plain,
% 1.72/1.96      ((((k2_funct_1 @ sk_C) = (sk_D))
% 1.72/1.96        | ~ (v1_relat_1 @ sk_D)
% 1.72/1.96        | ~ (v1_funct_1 @ sk_D)
% 1.72/1.96        | ~ (v2_funct_1 @ sk_D))),
% 1.72/1.96      inference('sup+', [status(thm)], ['105', '106'])).
% 1.72/1.96  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 1.72/1.96      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.96  thf('109', plain, ((v1_funct_1 @ sk_D)),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('110', plain, ((v2_funct_1 @ sk_D)),
% 1.72/1.96      inference('simplify', [status(thm)], ['103'])).
% 1.72/1.96  thf('111', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.72/1.96      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 1.72/1.96  thf('112', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.72/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.96  thf('113', plain, ($false),
% 1.72/1.96      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 1.72/1.96  
% 1.72/1.96  % SZS output end Refutation
% 1.72/1.96  
% 1.72/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
