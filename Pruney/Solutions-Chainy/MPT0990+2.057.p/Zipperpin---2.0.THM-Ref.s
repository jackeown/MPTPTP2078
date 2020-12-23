%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cnyvyaiHH2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 6.57s
% Output     : Refutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 187 expanded)
%              Number of leaves         :   43 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          : 1102 (4060 expanded)
%              Number of equality atoms :   76 ( 295 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X6 @ X7 @ X9 @ X10 @ X5 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ X1 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('33',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','47','50','51','52','57','71','72','75'])).

thf('77',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cnyvyaiHH2
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.57/6.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.57/6.75  % Solved by: fo/fo7.sh
% 6.57/6.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.57/6.75  % done 1485 iterations in 6.292s
% 6.57/6.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.57/6.75  % SZS output start Refutation
% 6.57/6.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.57/6.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.57/6.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.57/6.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.57/6.75  thf(sk_A_type, type, sk_A: $i).
% 6.57/6.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.57/6.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.57/6.75  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.57/6.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.57/6.75  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.57/6.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.57/6.75  thf(sk_B_type, type, sk_B: $i).
% 6.57/6.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.57/6.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.57/6.75  thf(sk_D_type, type, sk_D: $i).
% 6.57/6.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.57/6.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.57/6.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.57/6.75  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 6.57/6.75  thf(sk_C_type, type, sk_C: $i).
% 6.57/6.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.57/6.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.57/6.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.57/6.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.57/6.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.57/6.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.57/6.75  thf(t36_funct_2, conjecture,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.57/6.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.57/6.75       ( ![D:$i]:
% 6.57/6.75         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.57/6.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.57/6.75           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.57/6.75               ( r2_relset_1 @
% 6.57/6.75                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.57/6.75                 ( k6_partfun1 @ A ) ) & 
% 6.57/6.75               ( v2_funct_1 @ C ) ) =>
% 6.57/6.75             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.57/6.75               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 6.57/6.75  thf(zf_stmt_0, negated_conjecture,
% 6.57/6.75    (~( ![A:$i,B:$i,C:$i]:
% 6.57/6.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.57/6.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.57/6.75          ( ![D:$i]:
% 6.57/6.75            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.57/6.75                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.57/6.75              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.57/6.75                  ( r2_relset_1 @
% 6.57/6.75                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.57/6.75                    ( k6_partfun1 @ A ) ) & 
% 6.57/6.75                  ( v2_funct_1 @ C ) ) =>
% 6.57/6.75                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.57/6.75                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 6.57/6.75    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 6.57/6.75  thf('0', plain,
% 6.57/6.75      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.57/6.75        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.57/6.75        (k6_partfun1 @ sk_A))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(redefinition_k6_partfun1, axiom,
% 6.57/6.75    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.57/6.75  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.57/6.75  thf('2', plain,
% 6.57/6.75      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.57/6.75        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.57/6.75        (k6_relat_1 @ sk_A))),
% 6.57/6.75      inference('demod', [status(thm)], ['0', '1'])).
% 6.57/6.75  thf('3', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('4', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(redefinition_k1_partfun1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.57/6.75     ( ( ( v1_funct_1 @ E ) & 
% 6.57/6.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.57/6.75         ( v1_funct_1 @ F ) & 
% 6.57/6.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.57/6.75       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.57/6.75  thf('5', plain,
% 6.57/6.75      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.57/6.75         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 6.57/6.75          | ~ (v1_funct_1 @ X37)
% 6.57/6.75          | ~ (v1_funct_1 @ X40)
% 6.57/6.75          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.57/6.75          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 6.57/6.75              = (k5_relat_1 @ X37 @ X40)))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.57/6.75  thf('6', plain,
% 6.57/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.57/6.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.57/6.75            = (k5_relat_1 @ sk_C @ X0))
% 6.57/6.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.57/6.75          | ~ (v1_funct_1 @ X0)
% 6.57/6.75          | ~ (v1_funct_1 @ sk_C))),
% 6.57/6.75      inference('sup-', [status(thm)], ['4', '5'])).
% 6.57/6.75  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('8', plain,
% 6.57/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.57/6.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.57/6.75            = (k5_relat_1 @ sk_C @ X0))
% 6.57/6.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.57/6.75          | ~ (v1_funct_1 @ X0))),
% 6.57/6.75      inference('demod', [status(thm)], ['6', '7'])).
% 6.57/6.75  thf('9', plain,
% 6.57/6.75      ((~ (v1_funct_1 @ sk_D)
% 6.57/6.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.57/6.75            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.57/6.75      inference('sup-', [status(thm)], ['3', '8'])).
% 6.57/6.75  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('11', plain,
% 6.57/6.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.57/6.75         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.57/6.75      inference('demod', [status(thm)], ['9', '10'])).
% 6.57/6.75  thf('12', plain,
% 6.57/6.75      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.57/6.75        (k6_relat_1 @ sk_A))),
% 6.57/6.75      inference('demod', [status(thm)], ['2', '11'])).
% 6.57/6.75  thf('13', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('14', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(dt_k4_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.57/6.75     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.57/6.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.57/6.75       ( m1_subset_1 @
% 6.57/6.75         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.57/6.75         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 6.57/6.75  thf('15', plain,
% 6.57/6.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 6.57/6.75         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 6.57/6.75          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 6.57/6.75          | (m1_subset_1 @ (k4_relset_1 @ X6 @ X7 @ X9 @ X10 @ X5 @ X8) @ 
% 6.57/6.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X10))))),
% 6.57/6.75      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 6.57/6.75  thf('16', plain,
% 6.57/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.57/6.75         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.57/6.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.57/6.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 6.57/6.75      inference('sup-', [status(thm)], ['14', '15'])).
% 6.57/6.75  thf('17', plain,
% 6.57/6.75      ((m1_subset_1 @ 
% 6.57/6.75        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.57/6.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.57/6.75      inference('sup-', [status(thm)], ['13', '16'])).
% 6.57/6.75  thf(redefinition_r2_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i,D:$i]:
% 6.57/6.75     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.57/6.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.57/6.75       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.57/6.75  thf('18', plain,
% 6.57/6.75      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.57/6.75         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 6.57/6.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 6.57/6.75          | ((X23) = (X26))
% 6.57/6.75          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.57/6.75  thf('19', plain,
% 6.57/6.75      (![X0 : $i]:
% 6.57/6.75         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.57/6.75             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 6.57/6.75          | ((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 6.57/6.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.57/6.75      inference('sup-', [status(thm)], ['17', '18'])).
% 6.57/6.75  thf('20', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('21', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(redefinition_k4_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.57/6.75     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.57/6.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.57/6.75       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.57/6.75  thf('22', plain,
% 6.57/6.75      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 6.57/6.75         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 6.57/6.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 6.57/6.75          | ((k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20)
% 6.57/6.75              = (k5_relat_1 @ X17 @ X20)))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 6.57/6.75  thf('23', plain,
% 6.57/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.57/6.75         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.57/6.75            = (k5_relat_1 @ sk_C @ X0))
% 6.57/6.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.57/6.75      inference('sup-', [status(thm)], ['21', '22'])).
% 6.57/6.75  thf('24', plain,
% 6.57/6.75      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.57/6.75         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.57/6.75      inference('sup-', [status(thm)], ['20', '23'])).
% 6.57/6.75  thf('25', plain,
% 6.57/6.75      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.57/6.75         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.57/6.75      inference('sup-', [status(thm)], ['20', '23'])).
% 6.57/6.75  thf('26', plain,
% 6.57/6.75      (![X0 : $i]:
% 6.57/6.75         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 6.57/6.75          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 6.57/6.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.57/6.75      inference('demod', [status(thm)], ['19', '24', '25'])).
% 6.57/6.75  thf('27', plain,
% 6.57/6.75      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 6.57/6.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.57/6.75        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 6.57/6.75      inference('sup-', [status(thm)], ['12', '26'])).
% 6.57/6.75  thf(dt_k6_partfun1, axiom,
% 6.57/6.75    (![A:$i]:
% 6.57/6.75     ( ( m1_subset_1 @
% 6.57/6.75         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 6.57/6.75       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 6.57/6.75  thf('28', plain,
% 6.57/6.75      (![X36 : $i]:
% 6.57/6.75         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 6.57/6.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 6.57/6.75      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.57/6.75  thf('29', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.57/6.75  thf('30', plain,
% 6.57/6.75      (![X36 : $i]:
% 6.57/6.75         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 6.57/6.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 6.57/6.75      inference('demod', [status(thm)], ['28', '29'])).
% 6.57/6.75  thf('31', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 6.57/6.75      inference('demod', [status(thm)], ['27', '30'])).
% 6.57/6.75  thf(t63_funct_1, axiom,
% 6.57/6.75    (![A:$i]:
% 6.57/6.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.57/6.75       ( ![B:$i]:
% 6.57/6.75         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.57/6.75           ( ( ( v2_funct_1 @ A ) & 
% 6.57/6.75               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.57/6.75               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 6.57/6.75             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.57/6.75  thf('32', plain,
% 6.57/6.75      (![X0 : $i, X1 : $i]:
% 6.57/6.75         (~ (v1_relat_1 @ X0)
% 6.57/6.75          | ~ (v1_funct_1 @ X0)
% 6.57/6.75          | ((X0) = (k2_funct_1 @ X1))
% 6.57/6.75          | ((k5_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 6.57/6.75          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X0))
% 6.57/6.75          | ~ (v2_funct_1 @ X1)
% 6.57/6.75          | ~ (v1_funct_1 @ X1)
% 6.57/6.75          | ~ (v1_relat_1 @ X1))),
% 6.57/6.75      inference('cnf', [status(esa)], [t63_funct_1])).
% 6.57/6.75  thf('33', plain,
% 6.57/6.75      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 6.57/6.75        | ~ (v1_relat_1 @ sk_C)
% 6.57/6.75        | ~ (v1_funct_1 @ sk_C)
% 6.57/6.75        | ~ (v2_funct_1 @ sk_C)
% 6.57/6.75        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 6.57/6.75        | ((sk_D) = (k2_funct_1 @ sk_C))
% 6.57/6.75        | ~ (v1_funct_1 @ sk_D)
% 6.57/6.75        | ~ (v1_relat_1 @ sk_D))),
% 6.57/6.75      inference('sup-', [status(thm)], ['31', '32'])).
% 6.57/6.75  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(d1_funct_2, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.57/6.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.57/6.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.57/6.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.57/6.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.57/6.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.57/6.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.57/6.75  thf(zf_stmt_1, axiom,
% 6.57/6.75    (![C:$i,B:$i,A:$i]:
% 6.57/6.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.57/6.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.57/6.75  thf('35', plain,
% 6.57/6.75      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.57/6.75         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 6.57/6.75          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 6.57/6.75          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.57/6.75  thf('36', plain,
% 6.57/6.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 6.57/6.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 6.57/6.75      inference('sup-', [status(thm)], ['34', '35'])).
% 6.57/6.75  thf(zf_stmt_2, axiom,
% 6.57/6.75    (![B:$i,A:$i]:
% 6.57/6.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.57/6.75       ( zip_tseitin_0 @ B @ A ) ))).
% 6.57/6.75  thf('37', plain,
% 6.57/6.75      (![X27 : $i, X28 : $i]:
% 6.57/6.75         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.57/6.75  thf('38', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.57/6.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.57/6.75  thf(zf_stmt_5, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.57/6.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.57/6.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.57/6.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.57/6.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.57/6.75  thf('39', plain,
% 6.57/6.75      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.57/6.75         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.57/6.75          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.57/6.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.57/6.75  thf('40', plain,
% 6.57/6.75      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.57/6.75      inference('sup-', [status(thm)], ['38', '39'])).
% 6.57/6.75  thf('41', plain,
% 6.57/6.75      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 6.57/6.75      inference('sup-', [status(thm)], ['37', '40'])).
% 6.57/6.75  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('43', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 6.57/6.75      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 6.57/6.75  thf('44', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(redefinition_k1_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.57/6.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.57/6.75  thf('45', plain,
% 6.57/6.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.57/6.75         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 6.57/6.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.57/6.75  thf('46', plain,
% 6.57/6.75      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.57/6.75      inference('sup-', [status(thm)], ['44', '45'])).
% 6.57/6.75  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 6.57/6.75      inference('demod', [status(thm)], ['36', '43', '46'])).
% 6.57/6.75  thf('48', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(cc1_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.57/6.75       ( v1_relat_1 @ C ) ))).
% 6.57/6.75  thf('49', plain,
% 6.57/6.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.57/6.75         ((v1_relat_1 @ X2)
% 6.57/6.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 6.57/6.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.57/6.75  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 6.57/6.75      inference('sup-', [status(thm)], ['48', '49'])).
% 6.57/6.75  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('53', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf(redefinition_k2_relset_1, axiom,
% 6.57/6.75    (![A:$i,B:$i,C:$i]:
% 6.57/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.57/6.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.57/6.75  thf('54', plain,
% 6.57/6.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.57/6.75         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 6.57/6.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.57/6.75  thf('55', plain,
% 6.57/6.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.57/6.75      inference('sup-', [status(thm)], ['53', '54'])).
% 6.57/6.75  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.57/6.75      inference('sup+', [status(thm)], ['55', '56'])).
% 6.57/6.75  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('59', plain,
% 6.57/6.75      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.57/6.75         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 6.57/6.75          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 6.57/6.75          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.57/6.75  thf('60', plain,
% 6.57/6.75      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 6.57/6.75        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 6.57/6.75      inference('sup-', [status(thm)], ['58', '59'])).
% 6.57/6.75  thf('61', plain,
% 6.57/6.75      (![X27 : $i, X28 : $i]:
% 6.57/6.75         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.57/6.75  thf('62', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('63', plain,
% 6.57/6.75      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.57/6.75         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.57/6.75          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.57/6.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.57/6.75  thf('64', plain,
% 6.57/6.75      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 6.57/6.75      inference('sup-', [status(thm)], ['62', '63'])).
% 6.57/6.75  thf('65', plain,
% 6.57/6.75      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 6.57/6.75      inference('sup-', [status(thm)], ['61', '64'])).
% 6.57/6.75  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 6.57/6.75      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 6.57/6.75  thf('68', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('69', plain,
% 6.57/6.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.57/6.75         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 6.57/6.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.57/6.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.57/6.75  thf('70', plain,
% 6.57/6.75      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.57/6.75      inference('sup-', [status(thm)], ['68', '69'])).
% 6.57/6.75  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 6.57/6.75      inference('demod', [status(thm)], ['60', '67', '70'])).
% 6.57/6.75  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('73', plain,
% 6.57/6.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('74', plain,
% 6.57/6.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.57/6.75         ((v1_relat_1 @ X2)
% 6.57/6.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 6.57/6.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.57/6.75  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 6.57/6.75      inference('sup-', [status(thm)], ['73', '74'])).
% 6.57/6.75  thf('76', plain,
% 6.57/6.75      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 6.57/6.75        | ((sk_B) != (sk_B))
% 6.57/6.75        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 6.57/6.75      inference('demod', [status(thm)],
% 6.57/6.75                ['33', '47', '50', '51', '52', '57', '71', '72', '75'])).
% 6.57/6.75  thf('77', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 6.57/6.75      inference('simplify', [status(thm)], ['76'])).
% 6.57/6.75  thf('78', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 6.57/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.57/6.75  thf('79', plain, ($false),
% 6.57/6.75      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 6.57/6.75  
% 6.57/6.75  % SZS output end Refutation
% 6.57/6.75  
% 6.57/6.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
