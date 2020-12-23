%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WnTJsxHSQL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 176 expanded)
%              Number of leaves         :   42 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          : 1083 (3750 expanded)
%              Number of equality atoms :   77 ( 277 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X6 @ X7 @ X9 @ X10 @ X5 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

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

thf('29',plain,(
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

thf('30',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ X1 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','46','49','50','51','56','70','71','74'])).

thf('76',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WnTJsxHSQL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 311 iterations in 0.494s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.95  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.75/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.75/0.95  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.75/0.95  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.95  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.95  thf(t36_funct_2, conjecture,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.75/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.75/0.95           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.75/0.95               ( r2_relset_1 @
% 0.75/0.95                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.75/0.95                 ( k6_partfun1 @ A ) ) & 
% 0.75/0.95               ( v2_funct_1 @ C ) ) =>
% 0.75/0.95             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.95               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.95          ( ![D:$i]:
% 0.75/0.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.75/0.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.75/0.95              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.75/0.95                  ( r2_relset_1 @
% 0.75/0.95                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.75/0.95                    ( k6_partfun1 @ A ) ) & 
% 0.75/0.95                  ( v2_funct_1 @ C ) ) =>
% 0.75/0.95                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.95                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.75/0.95        (k6_partfun1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('2', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k1_partfun1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( v1_funct_1 @ F ) & 
% 0.75/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.95       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.75/0.95          | ~ (v1_funct_1 @ X36)
% 0.75/0.95          | ~ (v1_funct_1 @ X39)
% 0.75/0.95          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.75/0.95          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.75/0.95              = (k5_relat_1 @ X36 @ X39)))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.95            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.95  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.95            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.95          | ~ (v1_funct_1 @ X0))),
% 0.75/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.95  thf('7', plain,
% 0.75/0.95      ((~ (v1_funct_1 @ sk_D)
% 0.75/0.95        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.95            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['1', '6'])).
% 0.75/0.95  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.95         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.75/0.95      inference('demod', [status(thm)], ['7', '8'])).
% 0.75/0.95  thf('10', plain,
% 0.75/0.95      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.75/0.95        (k6_partfun1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['0', '9'])).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(dt_k4_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.95     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.95       ( m1_subset_1 @
% 0.75/0.95         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.95         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.75/0.95          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.75/0.95          | (m1_subset_1 @ (k4_relset_1 @ X6 @ X7 @ X9 @ X10 @ X5 @ X8) @ 
% 0.75/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X10))))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.95  thf('15', plain,
% 0.75/0.95      ((m1_subset_1 @ 
% 0.75/0.95        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['11', '14'])).
% 0.75/0.95  thf('16', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k4_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.95     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.95       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.75/0.95          | ((k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20)
% 0.75/0.95              = (k5_relat_1 @ X17 @ X20)))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.95            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.95         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.75/0.95      inference('sup-', [status(thm)], ['16', '19'])).
% 0.75/0.95  thf('21', plain,
% 0.75/0.95      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)], ['15', '20'])).
% 0.75/0.95  thf(redefinition_r2_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.95       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.75/0.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.75/0.95          | ((X23) = (X26))
% 0.75/0.95          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.75/0.95          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.95  thf('24', plain,
% 0.75/0.95      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['10', '23'])).
% 0.75/0.95  thf(t29_relset_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( m1_subset_1 @
% 0.75/0.95       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.75/0.95  thf('25', plain,
% 0.75/0.95      (![X27 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.75/0.95  thf(redefinition_k6_partfun1, axiom,
% 0.75/0.95    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.95  thf('26', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (![X27 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.75/0.95      inference('demod', [status(thm)], ['25', '26'])).
% 0.75/0.95  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '27'])).
% 0.75/0.95  thf(t63_funct_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.95           ( ( ( v2_funct_1 @ A ) & 
% 0.75/0.95               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.75/0.95               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.75/0.95             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ((X0) = (k2_funct_1 @ X1))
% 0.75/0.95          | ((k5_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.75/0.95          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.75/0.95          | ~ (v2_funct_1 @ X1)
% 0.75/0.95          | ~ (v1_funct_1 @ X1)
% 0.75/0.95          | ~ (v1_relat_1 @ X1))),
% 0.75/0.95      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.75/0.95  thf('30', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ((X0) = (k2_funct_1 @ X1))
% 0.75/0.95          | ((k5_relat_1 @ X1 @ X0) != (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.75/0.95          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.75/0.95          | ~ (v2_funct_1 @ X1)
% 0.75/0.95          | ~ (v1_funct_1 @ X1)
% 0.75/0.95          | ~ (v1_relat_1 @ X1))),
% 0.75/0.95      inference('demod', [status(thm)], ['29', '30'])).
% 0.75/0.95  thf('32', plain,
% 0.75/0.95      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.95        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.95        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.75/0.95        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.75/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.75/0.95        | ~ (v1_relat_1 @ sk_D))),
% 0.75/0.95      inference('sup-', [status(thm)], ['28', '31'])).
% 0.75/0.95  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(d1_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_1, axiom,
% 0.75/0.95    (![C:$i,B:$i,A:$i]:
% 0.75/0.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.95  thf('34', plain,
% 0.75/0.95      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.75/0.95         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.75/0.95          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.75/0.95          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.95  thf('35', plain,
% 0.75/0.95      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.75/0.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.95  thf(zf_stmt_2, axiom,
% 0.75/0.95    (![B:$i,A:$i]:
% 0.75/0.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.95       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.95  thf('36', plain,
% 0.75/0.95      (![X28 : $i, X29 : $i]:
% 0.75/0.95         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('37', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.95  thf(zf_stmt_5, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.95  thf('38', plain,
% 0.75/0.95      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.75/0.95         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.75/0.95          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.75/0.95          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.95  thf('39', plain,
% 0.75/0.95      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.95  thf('40', plain,
% 0.75/0.95      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['36', '39'])).
% 0.75/0.95  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('42', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.75/0.95      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.75/0.95  thf('43', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.95  thf('44', plain,
% 0.75/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.95         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.95  thf('45', plain,
% 0.75/0.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.75/0.95      inference('sup-', [status(thm)], ['43', '44'])).
% 0.75/0.95  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.75/0.95      inference('demod', [status(thm)], ['35', '42', '45'])).
% 0.75/0.95  thf('47', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(cc1_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( v1_relat_1 @ C ) ))).
% 0.75/0.95  thf('48', plain,
% 0.75/0.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.95         ((v1_relat_1 @ X2)
% 0.75/0.95          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.95  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.95      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.95  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('52', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.95  thf('53', plain,
% 0.75/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.75/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.95  thf('54', plain,
% 0.75/0.95      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.75/0.95      inference('sup-', [status(thm)], ['52', '53'])).
% 0.75/0.95  thf('55', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('56', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.75/0.95      inference('sup+', [status(thm)], ['54', '55'])).
% 0.75/0.95  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('58', plain,
% 0.75/0.95      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.75/0.95         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.75/0.95          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.75/0.95          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.95  thf('59', plain,
% 0.75/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.75/0.95        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['57', '58'])).
% 0.75/0.95  thf('60', plain,
% 0.75/0.95      (![X28 : $i, X29 : $i]:
% 0.75/0.95         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.95  thf('61', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('62', plain,
% 0.75/0.95      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.75/0.95         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.75/0.95          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.75/0.95          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.95  thf('63', plain,
% 0.75/0.95      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.95  thf('64', plain,
% 0.75/0.95      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['60', '63'])).
% 0.75/0.95  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('66', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.75/0.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.75/0.95  thf('67', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('68', plain,
% 0.75/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.95         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.95  thf('69', plain,
% 0.75/0.95      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.75/0.95      inference('sup-', [status(thm)], ['67', '68'])).
% 0.75/0.95  thf('70', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.75/0.95      inference('demod', [status(thm)], ['59', '66', '69'])).
% 0.75/0.95  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('72', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('73', plain,
% 0.75/0.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.95         ((v1_relat_1 @ X2)
% 0.75/0.95          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.95  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.75/0.95      inference('sup-', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('75', plain,
% 0.75/0.95      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.75/0.95        | ((sk_B) != (sk_B))
% 0.75/0.95        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['32', '46', '49', '50', '51', '56', '70', '71', '74'])).
% 0.75/0.95  thf('76', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.75/0.95      inference('simplify', [status(thm)], ['75'])).
% 0.75/0.95  thf('77', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('78', plain, ($false),
% 0.75/0.95      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
