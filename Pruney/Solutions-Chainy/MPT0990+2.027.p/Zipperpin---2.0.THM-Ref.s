%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dmw1Di3jbv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:58 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 564 expanded)
%              Number of leaves         :   48 ( 185 expanded)
%              Depth                    :   24
%              Number of atoms          : 1832 (13855 expanded)
%              Number of equality atoms :  111 ( 897 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('1',plain,(
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

thf('2',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_partfun1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('3',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41 ) @ ( k6_partfun1 @ X39 ) )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','44'])).

thf('46',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( zip_tseitin_0 @ X46 @ X49 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46 ) )
      | ( zip_tseitin_1 @ X48 @ X47 )
      | ( ( k2_relset_1 @ X50 @ X47 @ X49 )
       != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('56',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['54','57','58','59','60','61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v2_funct_1 @ X43 )
      | ~ ( zip_tseitin_0 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('69',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 )
        = ( k5_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('80',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X3 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','85','88'])).

thf('90',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['70','89'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('99',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_partfun1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ X0 ) )
        = sk_C ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ X0 ) )
        = sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('108',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('109',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('110',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['106','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('120',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','120'])).

thf('122',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['122','123','124'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('126',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('127',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('131',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dmw1Di3jbv
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.75/1.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.97  % Solved by: fo/fo7.sh
% 1.75/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.97  % done 1546 iterations in 1.502s
% 1.75/1.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.97  % SZS output start Refutation
% 1.75/1.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.75/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.75/1.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.75/1.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.75/1.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.75/1.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.75/1.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.75/1.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.75/1.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.75/1.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.97  thf(sk_D_type, type, sk_D: $i).
% 1.75/1.97  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.75/1.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.75/1.97  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.75/1.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.75/1.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.75/1.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.75/1.97  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.75/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.75/1.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.75/1.97  thf(dt_k2_funct_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.97       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.75/1.97         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.75/1.97  thf('0', plain,
% 1.75/1.97      (![X9 : $i]:
% 1.75/1.97         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.75/1.97          | ~ (v1_funct_1 @ X9)
% 1.75/1.97          | ~ (v1_relat_1 @ X9))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.75/1.97  thf(t36_funct_2, conjecture,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97       ( ![D:$i]:
% 1.75/1.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.97           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.75/1.97               ( r2_relset_1 @
% 1.75/1.97                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.75/1.97                 ( k6_partfun1 @ A ) ) & 
% 1.75/1.97               ( v2_funct_1 @ C ) ) =>
% 1.75/1.97             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.75/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.97    (~( ![A:$i,B:$i,C:$i]:
% 1.75/1.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97          ( ![D:$i]:
% 1.75/1.97            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.97                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.97              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.75/1.97                  ( r2_relset_1 @
% 1.75/1.97                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.75/1.97                    ( k6_partfun1 @ A ) ) & 
% 1.75/1.97                  ( v2_funct_1 @ C ) ) =>
% 1.75/1.97                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.75/1.97    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.75/1.97  thf('1', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(t35_funct_2, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.75/1.97         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.75/1.97             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.75/1.97  thf('2', plain,
% 1.75/1.97      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.75/1.97         (((X51) = (k1_xboole_0))
% 1.75/1.97          | ~ (v1_funct_1 @ X52)
% 1.75/1.97          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 1.75/1.97          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.75/1.97          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_partfun1 @ X53))
% 1.75/1.97          | ~ (v2_funct_1 @ X52)
% 1.75/1.97          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.75/1.97  thf('3', plain,
% 1.75/1.97      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.75/1.97        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['1', '2'])).
% 1.75/1.97  thf('4', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(redefinition_k2_relset_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.75/1.97  thf('5', plain,
% 1.75/1.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.75/1.97         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 1.75/1.97          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.75/1.97  thf('6', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['4', '5'])).
% 1.75/1.97  thf('7', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('9', plain,
% 1.75/1.97      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 1.75/1.97  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('11', plain,
% 1.75/1.97      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 1.75/1.97  thf('12', plain,
% 1.75/1.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.97        (k6_partfun1 @ sk_A))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('13', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('14', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(dt_k1_partfun1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.75/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.97         ( v1_funct_1 @ F ) & 
% 1.75/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.75/1.97       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.75/1.97         ( m1_subset_1 @
% 1.75/1.97           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.75/1.97           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.75/1.97  thf('15', plain,
% 1.75/1.97      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.75/1.97          | ~ (v1_funct_1 @ X25)
% 1.75/1.97          | ~ (v1_funct_1 @ X28)
% 1.75/1.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.75/1.97          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 1.75/1.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.75/1.97  thf('16', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.75/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.75/1.97          | ~ (v1_funct_1 @ X1)
% 1.75/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['14', '15'])).
% 1.75/1.97  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('18', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.75/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.75/1.97          | ~ (v1_funct_1 @ X1))),
% 1.75/1.97      inference('demod', [status(thm)], ['16', '17'])).
% 1.75/1.97  thf('19', plain,
% 1.75/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | (m1_subset_1 @ 
% 1.75/1.97           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.75/1.97      inference('sup-', [status(thm)], ['13', '18'])).
% 1.75/1.97  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('21', plain,
% 1.75/1.97      ((m1_subset_1 @ 
% 1.75/1.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.75/1.97      inference('demod', [status(thm)], ['19', '20'])).
% 1.75/1.97  thf(redefinition_r2_relset_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.75/1.97  thf('22', plain,
% 1.75/1.97      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.75/1.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.75/1.97          | ((X20) = (X23))
% 1.75/1.97          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.75/1.97  thf('23', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.97             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.75/1.97          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.75/1.97      inference('sup-', [status(thm)], ['21', '22'])).
% 1.75/1.97  thf('24', plain,
% 1.75/1.97      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.75/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.75/1.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.97            = (k6_partfun1 @ sk_A)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['12', '23'])).
% 1.75/1.97  thf(t29_relset_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( m1_subset_1 @
% 1.75/1.97       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.75/1.97  thf('25', plain,
% 1.75/1.97      (![X24 : $i]:
% 1.75/1.97         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 1.75/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.75/1.97  thf(redefinition_k6_partfun1, axiom,
% 1.75/1.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.75/1.97  thf('26', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.97  thf('27', plain,
% 1.75/1.97      (![X24 : $i]:
% 1.75/1.97         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 1.75/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 1.75/1.97      inference('demod', [status(thm)], ['25', '26'])).
% 1.75/1.97  thf('28', plain,
% 1.75/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.97         = (k6_partfun1 @ sk_A))),
% 1.75/1.97      inference('demod', [status(thm)], ['24', '27'])).
% 1.75/1.97  thf('29', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(t24_funct_2, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97       ( ![D:$i]:
% 1.75/1.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.97           ( ( r2_relset_1 @
% 1.75/1.97               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.75/1.97               ( k6_partfun1 @ B ) ) =>
% 1.75/1.97             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.75/1.97  thf('30', plain,
% 1.75/1.97      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X38)
% 1.75/1.97          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.75/1.97          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.75/1.97          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.75/1.97               (k1_partfun1 @ X39 @ X40 @ X40 @ X39 @ X38 @ X41) @ 
% 1.75/1.97               (k6_partfun1 @ X39))
% 1.75/1.97          | ((k2_relset_1 @ X40 @ X39 @ X41) = (X39))
% 1.75/1.97          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.75/1.97          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.75/1.97          | ~ (v1_funct_1 @ X41))),
% 1.75/1.97      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.75/1.97  thf('31', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.75/1.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.75/1.97               (k6_partfun1 @ sk_A))
% 1.75/1.97          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['29', '30'])).
% 1.75/1.97  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('34', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.97          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.75/1.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.97               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.75/1.97               (k6_partfun1 @ sk_A)))),
% 1.75/1.97      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.75/1.97  thf('35', plain,
% 1.75/1.97      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.75/1.97           (k6_partfun1 @ sk_A))
% 1.75/1.97        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.75/1.97        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.97        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['28', '34'])).
% 1.75/1.97  thf('36', plain,
% 1.75/1.97      (![X24 : $i]:
% 1.75/1.97         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 1.75/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 1.75/1.97      inference('demod', [status(thm)], ['25', '26'])).
% 1.75/1.97  thf('37', plain,
% 1.75/1.97      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.75/1.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.75/1.97          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 1.75/1.97          | ((X20) != (X23)))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.75/1.97  thf('38', plain,
% 1.75/1.97      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.75/1.97         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 1.75/1.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.75/1.97      inference('simplify', [status(thm)], ['37'])).
% 1.75/1.97  thf('39', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.75/1.97      inference('sup-', [status(thm)], ['36', '38'])).
% 1.75/1.97  thf('40', plain,
% 1.75/1.97      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['4', '5'])).
% 1.75/1.97  thf('41', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.75/1.97      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.75/1.97  thf('45', plain,
% 1.75/1.97      ((((sk_A) != (sk_A))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.97        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.75/1.97      inference('demod', [status(thm)], ['11', '44'])).
% 1.75/1.97  thf('46', plain,
% 1.75/1.97      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.97      inference('simplify', [status(thm)], ['45'])).
% 1.75/1.97  thf('47', plain,
% 1.75/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.97         = (k6_partfun1 @ sk_A))),
% 1.75/1.97      inference('demod', [status(thm)], ['24', '27'])).
% 1.75/1.97  thf('48', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(t30_funct_2, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.97         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.75/1.97       ( ![E:$i]:
% 1.75/1.97         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.75/1.97             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.75/1.97           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.75/1.97               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.75/1.97             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.75/1.97               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.75/1.97  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.75/1.97  thf(zf_stmt_2, axiom,
% 1.75/1.97    (![C:$i,B:$i]:
% 1.75/1.97     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.75/1.97       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.75/1.97  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.75/1.97  thf(zf_stmt_4, axiom,
% 1.75/1.97    (![E:$i,D:$i]:
% 1.75/1.97     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.75/1.97  thf(zf_stmt_5, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.75/1.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.97       ( ![E:$i]:
% 1.75/1.97         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.75/1.97             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.75/1.97           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.75/1.97               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.75/1.97             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.75/1.97  thf('49', plain,
% 1.75/1.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X46)
% 1.75/1.97          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.75/1.97          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.75/1.97          | (zip_tseitin_0 @ X46 @ X49)
% 1.75/1.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X47 @ X47 @ X48 @ X49 @ X46))
% 1.75/1.97          | (zip_tseitin_1 @ X48 @ X47)
% 1.75/1.97          | ((k2_relset_1 @ X50 @ X47 @ X49) != (X47))
% 1.75/1.97          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X47)))
% 1.75/1.97          | ~ (v1_funct_2 @ X49 @ X50 @ X47)
% 1.75/1.97          | ~ (v1_funct_1 @ X49))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.75/1.97  thf('50', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.75/1.97          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.75/1.97          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.75/1.97          | (zip_tseitin_0 @ sk_D @ X0)
% 1.75/1.97          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.97          | ~ (v1_funct_1 @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['48', '49'])).
% 1.75/1.97  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('53', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]:
% 1.75/1.97         (~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.75/1.97          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.75/1.97          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.75/1.97          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.75/1.97      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.75/1.97  thf('54', plain,
% 1.75/1.97      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.75/1.97        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.75/1.97        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.97        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.75/1.97        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.75/1.97        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['47', '53'])).
% 1.75/1.97  thf(fc4_funct_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.75/1.97       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.75/1.97  thf('55', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 1.75/1.97      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.75/1.97  thf('56', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.97  thf('57', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 1.75/1.97      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.97  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('59', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('60', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('62', plain,
% 1.75/1.97      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.75/1.97        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.97        | ((sk_B) != (sk_B)))),
% 1.75/1.97      inference('demod', [status(thm)], ['54', '57', '58', '59', '60', '61'])).
% 1.75/1.97  thf('63', plain,
% 1.75/1.97      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.75/1.97      inference('simplify', [status(thm)], ['62'])).
% 1.75/1.97  thf('64', plain,
% 1.75/1.97      (![X44 : $i, X45 : $i]:
% 1.75/1.97         (((X44) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X44 @ X45))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.75/1.97  thf('65', plain,
% 1.75/1.97      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['63', '64'])).
% 1.75/1.97  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('67', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 1.75/1.97  thf('68', plain,
% 1.75/1.97      (![X42 : $i, X43 : $i]:
% 1.75/1.97         ((v2_funct_1 @ X43) | ~ (zip_tseitin_0 @ X43 @ X42))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.75/1.97  thf('69', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['67', '68'])).
% 1.75/1.97  thf('70', plain,
% 1.75/1.97      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.75/1.97      inference('demod', [status(thm)], ['46', '69'])).
% 1.75/1.97  thf('71', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('72', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(redefinition_k1_partfun1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.75/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.97         ( v1_funct_1 @ F ) & 
% 1.75/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.75/1.97       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.75/1.97  thf('73', plain,
% 1.75/1.97      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.75/1.97          | ~ (v1_funct_1 @ X31)
% 1.75/1.97          | ~ (v1_funct_1 @ X34)
% 1.75/1.97          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.75/1.97          | ((k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)
% 1.75/1.97              = (k5_relat_1 @ X31 @ X34)))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.75/1.97  thf('74', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.75/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.75/1.97          | ~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['72', '73'])).
% 1.75/1.97  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('76', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.75/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.75/1.97          | ~ (v1_funct_1 @ X0))),
% 1.75/1.97      inference('demod', [status(thm)], ['74', '75'])).
% 1.75/1.97  thf('77', plain,
% 1.75/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.97            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['71', '76'])).
% 1.75/1.97  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('79', plain,
% 1.75/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.97         = (k6_partfun1 @ sk_A))),
% 1.75/1.97      inference('demod', [status(thm)], ['24', '27'])).
% 1.75/1.97  thf('80', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.75/1.97      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.75/1.97  thf(t55_relat_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( v1_relat_1 @ A ) =>
% 1.75/1.97       ( ![B:$i]:
% 1.75/1.97         ( ( v1_relat_1 @ B ) =>
% 1.75/1.97           ( ![C:$i]:
% 1.75/1.97             ( ( v1_relat_1 @ C ) =>
% 1.75/1.97               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.75/1.97                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.75/1.97  thf('81', plain,
% 1.75/1.97      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.97         (~ (v1_relat_1 @ X3)
% 1.75/1.97          | ((k5_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 1.75/1.97              = (k5_relat_1 @ X4 @ (k5_relat_1 @ X3 @ X5)))
% 1.75/1.97          | ~ (v1_relat_1 @ X5)
% 1.75/1.97          | ~ (v1_relat_1 @ X4))),
% 1.75/1.97      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.75/1.97  thf('82', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 1.75/1.97            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 1.75/1.97          | ~ (v1_relat_1 @ sk_C)
% 1.75/1.97          | ~ (v1_relat_1 @ X0)
% 1.75/1.97          | ~ (v1_relat_1 @ sk_D))),
% 1.75/1.97      inference('sup+', [status(thm)], ['80', '81'])).
% 1.75/1.97  thf('83', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(cc1_relset_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.97       ( v1_relat_1 @ C ) ))).
% 1.75/1.97  thf('84', plain,
% 1.75/1.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.75/1.97         ((v1_relat_1 @ X14)
% 1.75/1.97          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.75/1.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.75/1.97  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.97      inference('sup-', [status(thm)], ['83', '84'])).
% 1.75/1.97  thf('86', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('87', plain,
% 1.75/1.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.75/1.97         ((v1_relat_1 @ X14)
% 1.75/1.97          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.75/1.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.75/1.97  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.97  thf('89', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 1.75/1.97            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 1.75/1.97          | ~ (v1_relat_1 @ X0))),
% 1.75/1.97      inference('demod', [status(thm)], ['82', '85', '88'])).
% 1.75/1.97  thf('90', plain,
% 1.75/1.97      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 1.75/1.97          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 1.75/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.75/1.97      inference('sup+', [status(thm)], ['70', '89'])).
% 1.75/1.97  thf(d10_xboole_0, axiom,
% 1.75/1.97    (![A:$i,B:$i]:
% 1.75/1.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.75/1.97  thf('91', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.75/1.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.75/1.97  thf('92', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.75/1.97      inference('simplify', [status(thm)], ['91'])).
% 1.75/1.97  thf('93', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('94', plain,
% 1.75/1.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.75/1.97         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 1.75/1.97          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.75/1.97  thf('95', plain,
% 1.75/1.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['93', '94'])).
% 1.75/1.97  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.75/1.97      inference('sup+', [status(thm)], ['95', '96'])).
% 1.75/1.97  thf(t79_relat_1, axiom,
% 1.75/1.97    (![A:$i,B:$i]:
% 1.75/1.97     ( ( v1_relat_1 @ B ) =>
% 1.75/1.97       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.75/1.97         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.75/1.97  thf('98', plain,
% 1.75/1.97      (![X7 : $i, X8 : $i]:
% 1.75/1.97         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.75/1.97          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 1.75/1.97          | ~ (v1_relat_1 @ X7))),
% 1.75/1.97      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.75/1.97  thf('99', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.97  thf('100', plain,
% 1.75/1.97      (![X7 : $i, X8 : $i]:
% 1.75/1.97         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.75/1.97          | ((k5_relat_1 @ X7 @ (k6_partfun1 @ X8)) = (X7))
% 1.75/1.97          | ~ (v1_relat_1 @ X7))),
% 1.75/1.97      inference('demod', [status(thm)], ['98', '99'])).
% 1.75/1.97  thf('101', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (r1_tarski @ sk_B @ X0)
% 1.75/1.97          | ~ (v1_relat_1 @ sk_C)
% 1.75/1.97          | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ X0)) = (sk_C)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['97', '100'])).
% 1.75/1.97  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.97      inference('sup-', [status(thm)], ['83', '84'])).
% 1.75/1.97  thf('103', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (r1_tarski @ sk_B @ X0)
% 1.75/1.97          | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ X0)) = (sk_C)))),
% 1.75/1.97      inference('demod', [status(thm)], ['101', '102'])).
% 1.75/1.97  thf('104', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.75/1.97      inference('sup-', [status(thm)], ['92', '103'])).
% 1.75/1.97  thf('105', plain,
% 1.75/1.97      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))
% 1.75/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.75/1.97      inference('demod', [status(thm)], ['90', '104'])).
% 1.75/1.97  thf('106', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.75/1.97      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 1.75/1.97  thf('107', plain,
% 1.75/1.97      (![X9 : $i]:
% 1.75/1.97         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.75/1.97          | ~ (v1_funct_1 @ X9)
% 1.75/1.97          | ~ (v1_relat_1 @ X9))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.75/1.97  thf(t55_funct_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.97       ( ( v2_funct_1 @ A ) =>
% 1.75/1.97         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.75/1.97           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.75/1.97  thf('108', plain,
% 1.75/1.97      (![X12 : $i]:
% 1.75/1.97         (~ (v2_funct_1 @ X12)
% 1.75/1.97          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 1.75/1.97          | ~ (v1_funct_1 @ X12)
% 1.75/1.97          | ~ (v1_relat_1 @ X12))),
% 1.75/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.75/1.97  thf(t78_relat_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( v1_relat_1 @ A ) =>
% 1.75/1.97       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.75/1.97  thf('109', plain,
% 1.75/1.97      (![X6 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 1.75/1.97          | ~ (v1_relat_1 @ X6))),
% 1.75/1.97      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.75/1.97  thf('110', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.75/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.97  thf('111', plain,
% 1.75/1.97      (![X6 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 1.75/1.97          | ~ (v1_relat_1 @ X6))),
% 1.75/1.97      inference('demod', [status(thm)], ['109', '110'])).
% 1.75/1.97  thf('112', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.75/1.97            = (k2_funct_1 @ X0))
% 1.75/1.97          | ~ (v1_relat_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v2_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.75/1.97      inference('sup+', [status(thm)], ['108', '111'])).
% 1.75/1.97  thf('113', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (v1_relat_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v2_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_relat_1 @ X0)
% 1.75/1.97          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.75/1.97              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['107', '112'])).
% 1.75/1.97  thf('114', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.75/1.97            = (k2_funct_1 @ X0))
% 1.75/1.97          | ~ (v2_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_funct_1 @ X0)
% 1.75/1.97          | ~ (v1_relat_1 @ X0))),
% 1.75/1.97      inference('simplify', [status(thm)], ['113'])).
% 1.75/1.97  thf('115', plain,
% 1.75/1.97      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 1.75/1.97          = (k2_funct_1 @ sk_D))
% 1.75/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.97      inference('sup+', [status(thm)], ['106', '114'])).
% 1.75/1.97  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.97  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('118', plain,
% 1.75/1.97      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 1.75/1.97          = (k2_funct_1 @ sk_D))
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.97      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.75/1.97  thf('119', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['67', '68'])).
% 1.75/1.97  thf('120', plain,
% 1.75/1.97      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 1.75/1.97         = (k2_funct_1 @ sk_D))),
% 1.75/1.97      inference('demod', [status(thm)], ['118', '119'])).
% 1.75/1.97  thf('121', plain,
% 1.75/1.97      ((((k2_funct_1 @ sk_D) = (sk_C)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.75/1.97      inference('demod', [status(thm)], ['105', '120'])).
% 1.75/1.97  thf('122', plain,
% 1.75/1.97      ((~ (v1_relat_1 @ sk_D)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['0', '121'])).
% 1.75/1.97  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.97  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('125', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 1.75/1.97      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.75/1.97  thf(t65_funct_1, axiom,
% 1.75/1.97    (![A:$i]:
% 1.75/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.97       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.75/1.97  thf('126', plain,
% 1.75/1.97      (![X13 : $i]:
% 1.75/1.97         (~ (v2_funct_1 @ X13)
% 1.75/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 1.75/1.97          | ~ (v1_funct_1 @ X13)
% 1.75/1.97          | ~ (v1_relat_1 @ X13))),
% 1.75/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.75/1.97  thf('127', plain,
% 1.75/1.97      ((((k2_funct_1 @ sk_C) = (sk_D))
% 1.75/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.75/1.97        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.97        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.97      inference('sup+', [status(thm)], ['125', '126'])).
% 1.75/1.97  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.97  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['67', '68'])).
% 1.75/1.97  thf('131', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.75/1.97      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 1.75/1.97  thf('132', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('133', plain, ($false),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 1.75/1.97  
% 1.75/1.97  % SZS output end Refutation
% 1.75/1.97  
% 1.82/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
