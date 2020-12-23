%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ts8QPmeGXf

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:01 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 915 expanded)
%              Number of leaves         :   51 ( 297 expanded)
%              Depth                    :   21
%              Number of atoms          : 2599 (21634 expanded)
%              Number of equality atoms :  125 ( 301 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) )
      | ~ ( v3_funct_2 @ X43 @ X42 @ X42 )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X42 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_funct_2 @ X47 @ X46 )
        = ( k2_funct_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X47 ) ) )
      | ~ ( v3_funct_2 @ X46 @ X47 @ X47 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X47 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(t54_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ( r2_relset_1 @ X31 @ X31 @ X32 @ X30 )
      | ( r2_hidden @ ( sk_D @ X30 @ X32 @ X31 ) @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B_1 ) @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B_1 ) @ sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('21',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B_1 ) @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['18','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('36',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('39',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ( X60
        = ( k2_funct_1 @ X63 ) )
      | ~ ( r2_relset_1 @ X62 @ X62 @ ( k1_partfun1 @ X62 @ X61 @ X61 @ X62 @ X63 @ X60 ) @ ( k6_partfun1 @ X62 ) )
      | ( X61 = k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X63 )
      | ( ( k2_relset_1 @ X62 @ X61 @ X63 )
       != X61 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X61 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('57',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
     != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','49','50','51','52','55','61'])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf('65',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X55 @ X54 @ ( k1_partfun1 @ X55 @ X53 @ X53 @ X54 @ X56 @ X52 ) )
       != X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X56 )
        = X53 )
      | ( X54 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X55 @ X53 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t28_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_relset_1 @ X1 @ sk_A @ X0 )
        = sk_A )
      | ( ( k2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) )
       != sk_A )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_relset_1 @ X1 @ sk_A @ X0 )
        = sk_A )
      | ( ( k2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) )
       != sk_A ) ) ),
    inference(demod,[status(thm)],['66','72','73','74'])).

thf('76',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) )
     != sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('78',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','79','80','81','82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('86',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('87',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','90','91','92','93'])).

thf('95',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('97',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51 ) @ ( k6_partfun1 @ X49 ) )
      | ( ( k2_relset_1 @ X50 @ X49 @ X51 )
        = X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['102','103','104','105','106','107'])).

thf('109',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','108'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('112',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('114',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k1_relset_1 @ X64 @ X64 @ X65 )
        = X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X64 ) ) )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X64 )
      | ~ ( v1_funct_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('120',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['115','116','117','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('123',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('127',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','121','124','125','126'])).

thf('128',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference(clc,[status(thm)],['84','127'])).

thf('129',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','128'])).

thf('130',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('131',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('134',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['131','134'])).

thf('137',plain,(
    r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B_1 ) @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['22','135','136'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('138',plain,(
    ! [X3: $i] :
      ( v1_xboole_0 @ ( sk_B @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('139',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('140',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('142',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relset_1 @ X0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('145',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['138','147'])).

thf('149',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('150',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('151',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ( r2_relset_1 @ X31 @ X31 @ X32 @ X30 )
      | ( r2_hidden @ ( sk_D @ X30 @ X32 @ X31 ) @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k6_partfun1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('155',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('159',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('160',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['157','162'])).

thf('164',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','163'])).

thf('165',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('166',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('171',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) )
      = ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['169','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,(
    ! [X3: $i] :
      ( v1_xboole_0 @ ( sk_B @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('176',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('177',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['174','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('183',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['174','179'])).

thf('187',plain,(
    r2_relset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('189',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_relset_1 @ X1 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X2 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('193',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['180','193'])).

thf('195',plain,(
    $false ),
    inference('sup-',[status(thm)],['137','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ts8QPmeGXf
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.19/3.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.19/3.43  % Solved by: fo/fo7.sh
% 3.19/3.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.19/3.43  % done 3239 iterations in 2.955s
% 3.19/3.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.19/3.43  % SZS output start Refutation
% 3.19/3.43  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.19/3.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.19/3.43  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.19/3.43  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.19/3.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.19/3.43  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.19/3.43  thf(sk_A_type, type, sk_A: $i).
% 3.19/3.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.19/3.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.19/3.43  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.19/3.43  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.19/3.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.19/3.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.19/3.43  thf(sk_C_type, type, sk_C: $i).
% 3.19/3.43  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 3.19/3.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.19/3.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.19/3.43  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.19/3.43  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.19/3.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.19/3.43  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.19/3.43  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.19/3.43  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.19/3.43  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 3.19/3.43  thf(sk_B_type, type, sk_B: $i > $i).
% 3.19/3.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.19/3.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.19/3.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.19/3.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.19/3.43  thf(t87_funct_2, conjecture,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( v3_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43       ( ![C:$i]:
% 3.19/3.43         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 3.19/3.43             ( v3_funct_2 @ C @ A @ A ) & 
% 3.19/3.43             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43           ( ( r2_relset_1 @
% 3.19/3.43               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 3.19/3.43               ( k6_partfun1 @ A ) ) =>
% 3.19/3.43             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 3.19/3.43  thf(zf_stmt_0, negated_conjecture,
% 3.19/3.43    (~( ![A:$i,B:$i]:
% 3.19/3.43        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.19/3.43            ( v3_funct_2 @ B @ A @ A ) & 
% 3.19/3.43            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43          ( ![C:$i]:
% 3.19/3.43            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 3.19/3.43                ( v3_funct_2 @ C @ A @ A ) & 
% 3.19/3.43                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43              ( ( r2_relset_1 @
% 3.19/3.43                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 3.19/3.43                  ( k6_partfun1 @ A ) ) =>
% 3.19/3.43                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 3.19/3.43    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 3.19/3.43  thf('0', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('1', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(dt_k2_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( v3_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 3.19/3.43         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.19/3.43         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.19/3.43         ( m1_subset_1 @
% 3.19/3.43           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 3.19/3.43  thf('2', plain,
% 3.19/3.43      (![X42 : $i, X43 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k2_funct_2 @ X42 @ X43) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))
% 3.19/3.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))
% 3.19/3.43          | ~ (v3_funct_2 @ X43 @ X42 @ X42)
% 3.19/3.43          | ~ (v1_funct_2 @ X43 @ X42 @ X42)
% 3.19/3.43          | ~ (v1_funct_1 @ X43))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.19/3.43  thf('3', plain,
% 3.19/3.43      ((~ (v1_funct_1 @ sk_B_1)
% 3.19/3.43        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['1', '2'])).
% 3.19/3.43  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('6', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('7', plain,
% 3.19/3.43      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 3.19/3.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 3.19/3.43  thf('8', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(redefinition_k2_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( v3_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 3.19/3.43  thf('9', plain,
% 3.19/3.43      (![X46 : $i, X47 : $i]:
% 3.19/3.43         (((k2_funct_2 @ X47 @ X46) = (k2_funct_1 @ X46))
% 3.19/3.43          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X47)))
% 3.19/3.43          | ~ (v3_funct_2 @ X46 @ X47 @ X47)
% 3.19/3.43          | ~ (v1_funct_2 @ X46 @ X47 @ X47)
% 3.19/3.43          | ~ (v1_funct_1 @ X46))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 3.19/3.43  thf('10', plain,
% 3.19/3.43      ((~ (v1_funct_1 @ sk_B_1)
% 3.19/3.43        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['8', '9'])).
% 3.19/3.43  thf('11', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('12', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('13', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('14', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 3.19/3.43  thf('15', plain,
% 3.19/3.43      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 3.19/3.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('demod', [status(thm)], ['7', '14'])).
% 3.19/3.43  thf(t54_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 3.19/3.43       ( ![C:$i]:
% 3.19/3.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 3.19/3.43           ( ( ![D:$i]:
% 3.19/3.43               ( ( r2_hidden @ D @ A ) =>
% 3.19/3.43                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 3.19/3.43             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 3.19/3.43  thf('16', plain,
% 3.19/3.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 3.19/3.43          | (r2_relset_1 @ X31 @ X31 @ X32 @ X30)
% 3.19/3.43          | (r2_hidden @ (sk_D @ X30 @ X32 @ X31) @ X31)
% 3.19/3.43          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31))))),
% 3.19/3.43      inference('cnf', [status(esa)], [t54_relset_1])).
% 3.19/3.43  thf('17', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | (r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B_1) @ X0 @ sk_A) @ sk_A)
% 3.19/3.43          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ (k2_funct_1 @ sk_B_1)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['15', '16'])).
% 3.19/3.43  thf('18', plain,
% 3.19/3.43      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))
% 3.19/3.43        | (r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B_1) @ sk_C @ sk_A) @ sk_A))),
% 3.19/3.43      inference('sup-', [status(thm)], ['0', '17'])).
% 3.19/3.43  thf('19', plain,
% 3.19/3.43      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 3.19/3.43  thf('21', plain,
% 3.19/3.43      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('demod', [status(thm)], ['19', '20'])).
% 3.19/3.43  thf('22', plain,
% 3.19/3.43      ((r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B_1) @ sk_C @ sk_A) @ sk_A)),
% 3.19/3.43      inference('clc', [status(thm)], ['18', '21'])).
% 3.19/3.43  thf('23', plain,
% 3.19/3.43      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 3.19/3.43        (k6_partfun1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('24', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('25', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(dt_k1_partfun1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ E ) & 
% 3.19/3.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.19/3.43         ( v1_funct_1 @ F ) & 
% 3.19/3.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.19/3.43       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.19/3.43         ( m1_subset_1 @
% 3.19/3.43           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.19/3.43           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.19/3.43  thf('26', plain,
% 3.19/3.43      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.19/3.43          | ~ (v1_funct_1 @ X36)
% 3.19/3.43          | ~ (v1_funct_1 @ X39)
% 3.19/3.43          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.19/3.43          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 3.19/3.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.19/3.43  thf('27', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.19/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.19/3.43          | ~ (v1_funct_1 @ X1)
% 3.19/3.43          | ~ (v1_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['25', '26'])).
% 3.19/3.43  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('29', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.19/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.19/3.43          | ~ (v1_funct_1 @ X1))),
% 3.19/3.43      inference('demod', [status(thm)], ['27', '28'])).
% 3.19/3.43  thf('30', plain,
% 3.19/3.43      ((~ (v1_funct_1 @ sk_C)
% 3.19/3.43        | (m1_subset_1 @ 
% 3.19/3.43           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['24', '29'])).
% 3.19/3.43  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('32', plain,
% 3.19/3.43      ((m1_subset_1 @ 
% 3.19/3.43        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 3.19/3.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('demod', [status(thm)], ['30', '31'])).
% 3.19/3.43  thf(redefinition_r2_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i,D:$i]:
% 3.19/3.43     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.19/3.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.43       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.19/3.43  thf('33', plain,
% 3.19/3.43      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ((X26) = (X29))
% 3.19/3.43          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.19/3.43  thf('34', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ X0)
% 3.19/3.43          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) = (X0))
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['32', '33'])).
% 3.19/3.43  thf('35', plain,
% 3.19/3.43      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.19/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 3.19/3.43            = (k6_partfun1 @ sk_A)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['23', '34'])).
% 3.19/3.43  thf(dt_k6_partfun1, axiom,
% 3.19/3.43    (![A:$i]:
% 3.19/3.43     ( ( m1_subset_1 @
% 3.19/3.43         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.19/3.43       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.19/3.43  thf('36', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('37', plain,
% 3.19/3.43      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 3.19/3.43         = (k6_partfun1 @ sk_A))),
% 3.19/3.43      inference('demod', [status(thm)], ['35', '36'])).
% 3.19/3.43  thf('38', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(t36_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.43       ( ![D:$i]:
% 3.19/3.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.19/3.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.19/3.43           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.19/3.43               ( r2_relset_1 @
% 3.19/3.43                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.19/3.43                 ( k6_partfun1 @ A ) ) & 
% 3.19/3.43               ( v2_funct_1 @ C ) ) =>
% 3.19/3.43             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.19/3.43               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.19/3.43  thf('39', plain,
% 3.19/3.43      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X60)
% 3.19/3.43          | ~ (v1_funct_2 @ X60 @ X61 @ X62)
% 3.19/3.43          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 3.19/3.43          | ((X60) = (k2_funct_1 @ X63))
% 3.19/3.43          | ~ (r2_relset_1 @ X62 @ X62 @ 
% 3.19/3.43               (k1_partfun1 @ X62 @ X61 @ X61 @ X62 @ X63 @ X60) @ 
% 3.19/3.43               (k6_partfun1 @ X62))
% 3.19/3.43          | ((X61) = (k1_xboole_0))
% 3.19/3.43          | ((X62) = (k1_xboole_0))
% 3.19/3.43          | ~ (v2_funct_1 @ X63)
% 3.19/3.43          | ((k2_relset_1 @ X62 @ X61 @ X63) != (X61))
% 3.19/3.43          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61)))
% 3.19/3.43          | ~ (v1_funct_2 @ X63 @ X62 @ X61)
% 3.19/3.43          | ~ (v1_funct_1 @ X63))),
% 3.19/3.43      inference('cnf', [status(esa)], [t36_funct_2])).
% 3.19/3.43  thf('40', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.19/3.43          | ~ (v2_funct_1 @ X0)
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.19/3.43               (k6_partfun1 @ sk_A))
% 3.19/3.43          | ((sk_C) = (k2_funct_1 @ X0))
% 3.19/3.43          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43          | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['38', '39'])).
% 3.19/3.43  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('43', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.19/3.43          | ~ (v2_funct_1 @ X0)
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.19/3.43               (k6_partfun1 @ sk_A))
% 3.19/3.43          | ((sk_C) = (k2_funct_1 @ X0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['40', '41', '42'])).
% 3.19/3.43  thf('44', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((sk_C) = (k2_funct_1 @ X0))
% 3.19/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 3.19/3.43               (k6_partfun1 @ sk_A))
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ~ (v2_funct_1 @ X0)
% 3.19/3.43          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (v1_funct_1 @ X0))),
% 3.19/3.43      inference('simplify', [status(thm)], ['43'])).
% 3.19/3.43  thf('45', plain,
% 3.19/3.43      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.19/3.43           (k6_partfun1 @ sk_A))
% 3.19/3.43        | ~ (v1_funct_1 @ sk_B_1)
% 3.19/3.43        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 3.19/3.43        | ~ (v2_funct_1 @ sk_B_1)
% 3.19/3.43        | ((sk_A) = (k1_xboole_0))
% 3.19/3.43        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['37', '44'])).
% 3.19/3.43  thf('46', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('47', plain,
% 3.19/3.43      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 3.19/3.43          | ((X26) != (X29)))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.19/3.43  thf('48', plain,
% 3.19/3.43      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.19/3.43      inference('simplify', [status(thm)], ['47'])).
% 3.19/3.43  thf('49', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['46', '48'])).
% 3.19/3.43  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('51', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('52', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('53', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(redefinition_k2_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.19/3.43  thf('54', plain,
% 3.19/3.43      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.19/3.43         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.19/3.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.43  thf('55', plain,
% 3.19/3.43      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['53', '54'])).
% 3.19/3.43  thf('56', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(cc2_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.43       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 3.19/3.43         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 3.19/3.43  thf('57', plain,
% 3.19/3.43      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X33)
% 3.19/3.43          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 3.19/3.43          | (v2_funct_1 @ X33)
% 3.19/3.43          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 3.19/3.43      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.19/3.43  thf('58', plain,
% 3.19/3.43      (((v2_funct_1 @ sk_B_1)
% 3.19/3.43        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['56', '57'])).
% 3.19/3.43  thf('59', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('60', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('demod', [status(thm)], ['58', '59', '60'])).
% 3.19/3.43  thf('62', plain,
% 3.19/3.43      ((((k2_relat_1 @ sk_B_1) != (sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0))
% 3.19/3.43        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 3.19/3.43      inference('demod', [status(thm)],
% 3.19/3.43                ['45', '49', '50', '51', '52', '55', '61'])).
% 3.19/3.43  thf('63', plain,
% 3.19/3.43      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 3.19/3.43         = (k6_partfun1 @ sk_A))),
% 3.19/3.43      inference('demod', [status(thm)], ['35', '36'])).
% 3.19/3.43  thf('64', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(t28_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i,D:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.19/3.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.43       ( ![E:$i]:
% 3.19/3.43         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.19/3.43             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.19/3.43           ( ( ( ( k2_relset_1 @
% 3.19/3.43                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 3.19/3.43                 ( C ) ) & 
% 3.19/3.43               ( v2_funct_1 @ E ) ) =>
% 3.19/3.43             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.19/3.43               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 3.19/3.43  thf('65', plain,
% 3.19/3.43      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X52)
% 3.19/3.43          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 3.19/3.43          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 3.19/3.43          | ~ (v2_funct_1 @ X52)
% 3.19/3.43          | ((k2_relset_1 @ X55 @ X54 @ 
% 3.19/3.43              (k1_partfun1 @ X55 @ X53 @ X53 @ X54 @ X56 @ X52)) != (X54))
% 3.19/3.43          | ((k2_relset_1 @ X55 @ X53 @ X56) = (X53))
% 3.19/3.43          | ((X54) = (k1_xboole_0))
% 3.19/3.43          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 3.19/3.43          | ~ (v1_funct_2 @ X56 @ X55 @ X53)
% 3.19/3.43          | ~ (v1_funct_1 @ X56))),
% 3.19/3.43      inference('cnf', [status(esa)], [t28_funct_2])).
% 3.19/3.43  thf('66', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ((k2_relset_1 @ X1 @ sk_A @ X0) = (sk_A))
% 3.19/3.43          | ((k2_relset_1 @ X1 @ sk_A @ 
% 3.19/3.43              (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C)) != (
% 3.19/3.43              sk_A))
% 3.19/3.43          | ~ (v2_funct_1 @ sk_C)
% 3.19/3.43          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43          | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['64', '65'])).
% 3.19/3.43  thf('67', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('68', plain,
% 3.19/3.43      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X33)
% 3.19/3.43          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 3.19/3.43          | (v2_funct_1 @ X33)
% 3.19/3.43          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 3.19/3.43      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.19/3.43  thf('69', plain,
% 3.19/3.43      (((v2_funct_1 @ sk_C)
% 3.19/3.43        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['67', '68'])).
% 3.19/3.43  thf('70', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 3.19/3.43      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.19/3.43  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('75', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 3.19/3.43          | ((sk_A) = (k1_xboole_0))
% 3.19/3.43          | ((k2_relset_1 @ X1 @ sk_A @ X0) = (sk_A))
% 3.19/3.43          | ((k2_relset_1 @ X1 @ sk_A @ 
% 3.19/3.43              (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C)) != (
% 3.19/3.43              sk_A)))),
% 3.19/3.43      inference('demod', [status(thm)], ['66', '72', '73', '74'])).
% 3.19/3.43  thf('76', plain,
% 3.19/3.43      ((((k2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A)) != (sk_A))
% 3.19/3.43        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0))
% 3.19/3.43        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['63', '75'])).
% 3.19/3.43  thf('77', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('78', plain,
% 3.19/3.43      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.19/3.43         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.19/3.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.43  thf('79', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0))
% 3.19/3.43           = (k2_relat_1 @ (k6_partfun1 @ X0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['77', '78'])).
% 3.19/3.43  thf('80', plain,
% 3.19/3.43      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['53', '54'])).
% 3.19/3.43  thf('81', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('82', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('83', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('84', plain,
% 3.19/3.43      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) != (sk_A))
% 3.19/3.43        | ((k2_relat_1 @ sk_B_1) = (sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['76', '79', '80', '81', '82', '83'])).
% 3.19/3.43  thf('85', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(t35_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.43       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.19/3.43         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.19/3.43           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.19/3.43             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.19/3.43  thf('86', plain,
% 3.19/3.43      (![X57 : $i, X58 : $i, X59 : $i]:
% 3.19/3.43         (((X57) = (k1_xboole_0))
% 3.19/3.43          | ~ (v1_funct_1 @ X58)
% 3.19/3.43          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 3.19/3.43          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 3.19/3.43          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 3.19/3.43          | ~ (v2_funct_1 @ X58)
% 3.19/3.43          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.19/3.43  thf('87', plain,
% 3.19/3.43      ((((k2_relset_1 @ sk_A @ sk_A @ sk_C) != (sk_A))
% 3.19/3.43        | ~ (v2_funct_1 @ sk_C)
% 3.19/3.43        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 3.19/3.43        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_C)
% 3.19/3.43        | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['85', '86'])).
% 3.19/3.43  thf('88', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('89', plain,
% 3.19/3.43      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.19/3.43         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.19/3.43          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.43  thf('90', plain,
% 3.19/3.43      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['88', '89'])).
% 3.19/3.43  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 3.19/3.43      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.19/3.43  thf('92', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('94', plain,
% 3.19/3.43      ((((k2_relat_1 @ sk_C) != (sk_A))
% 3.19/3.43        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['87', '90', '91', '92', '93'])).
% 3.19/3.43  thf('95', plain,
% 3.19/3.43      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 3.19/3.43         = (k6_partfun1 @ sk_A))),
% 3.19/3.43      inference('demod', [status(thm)], ['35', '36'])).
% 3.19/3.43  thf('96', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(t24_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.43       ( ![D:$i]:
% 3.19/3.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.19/3.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.19/3.43           ( ( r2_relset_1 @
% 3.19/3.43               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.19/3.43               ( k6_partfun1 @ B ) ) =>
% 3.19/3.43             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.19/3.43  thf('97', plain,
% 3.19/3.43      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X48)
% 3.19/3.43          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 3.19/3.43          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 3.19/3.43          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 3.19/3.43               (k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51) @ 
% 3.19/3.43               (k6_partfun1 @ X49))
% 3.19/3.43          | ((k2_relset_1 @ X50 @ X49 @ X51) = (X49))
% 3.19/3.43          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 3.19/3.43          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 3.19/3.43          | ~ (v1_funct_1 @ X51))),
% 3.19/3.43      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.19/3.43  thf('98', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | ((k2_relset_1 @ sk_A @ sk_A @ X0) = (sk_A))
% 3.19/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ X0) @ 
% 3.19/3.43               (k6_partfun1 @ sk_A))
% 3.19/3.43          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (v1_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['96', '97'])).
% 3.19/3.43  thf('99', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('100', plain, ((v1_funct_1 @ sk_B_1)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('101', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_funct_1 @ X0)
% 3.19/3.43          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 3.19/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43          | ((k2_relset_1 @ sk_A @ sk_A @ X0) = (sk_A))
% 3.19/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.43               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ X0) @ 
% 3.19/3.43               (k6_partfun1 @ sk_A)))),
% 3.19/3.43      inference('demod', [status(thm)], ['98', '99', '100'])).
% 3.19/3.43  thf('102', plain,
% 3.19/3.43      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.19/3.43           (k6_partfun1 @ sk_A))
% 3.19/3.43        | ((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))
% 3.19/3.43        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.43        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['95', '101'])).
% 3.19/3.43  thf('103', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['46', '48'])).
% 3.19/3.43  thf('104', plain,
% 3.19/3.43      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['88', '89'])).
% 3.19/3.43  thf('105', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('106', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('108', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 3.19/3.43      inference('demod', [status(thm)],
% 3.19/3.43                ['102', '103', '104', '105', '106', '107'])).
% 3.19/3.43  thf('109', plain,
% 3.19/3.43      ((((sk_A) != (sk_A))
% 3.19/3.43        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['94', '108'])).
% 3.19/3.43  thf('110', plain,
% 3.19/3.43      ((((sk_A) = (k1_xboole_0))
% 3.19/3.43        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 3.19/3.43      inference('simplify', [status(thm)], ['109'])).
% 3.19/3.43  thf(t58_funct_1, axiom,
% 3.19/3.43    (![A:$i]:
% 3.19/3.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.19/3.43       ( ( v2_funct_1 @ A ) =>
% 3.19/3.43         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.19/3.43             ( k1_relat_1 @ A ) ) & 
% 3.19/3.43           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.19/3.43             ( k1_relat_1 @ A ) ) ) ) ))).
% 3.19/3.43  thf('111', plain,
% 3.19/3.43      (![X13 : $i]:
% 3.19/3.43         (~ (v2_funct_1 @ X13)
% 3.19/3.43          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 3.19/3.43              = (k1_relat_1 @ X13))
% 3.19/3.43          | ~ (v1_funct_1 @ X13)
% 3.19/3.43          | ~ (v1_relat_1 @ X13))),
% 3.19/3.43      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.19/3.43  thf('112', plain,
% 3.19/3.43      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0))
% 3.19/3.43        | ~ (v1_relat_1 @ sk_C)
% 3.19/3.43        | ~ (v1_funct_1 @ sk_C)
% 3.19/3.43        | ~ (v2_funct_1 @ sk_C))),
% 3.19/3.43      inference('sup+', [status(thm)], ['110', '111'])).
% 3.19/3.43  thf('113', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(t67_funct_2, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.19/3.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.19/3.43       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 3.19/3.43  thf('114', plain,
% 3.19/3.43      (![X64 : $i, X65 : $i]:
% 3.19/3.43         (((k1_relset_1 @ X64 @ X64 @ X65) = (X64))
% 3.19/3.43          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X64)))
% 3.19/3.43          | ~ (v1_funct_2 @ X65 @ X64 @ X64)
% 3.19/3.43          | ~ (v1_funct_1 @ X65))),
% 3.19/3.43      inference('cnf', [status(esa)], [t67_funct_2])).
% 3.19/3.43  thf('115', plain,
% 3.19/3.43      ((~ (v1_funct_1 @ sk_C)
% 3.19/3.43        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 3.19/3.43        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['113', '114'])).
% 3.19/3.43  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('118', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(redefinition_k1_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.43       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.19/3.43  thf('119', plain,
% 3.19/3.43      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.19/3.43         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.19/3.43          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.19/3.43  thf('120', plain,
% 3.19/3.43      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['118', '119'])).
% 3.19/3.43  thf('121', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 3.19/3.43      inference('demod', [status(thm)], ['115', '116', '117', '120'])).
% 3.19/3.43  thf('122', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(cc1_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.43       ( v1_relat_1 @ C ) ))).
% 3.19/3.43  thf('123', plain,
% 3.19/3.43      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.19/3.43         ((v1_relat_1 @ X14)
% 3.19/3.43          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.19/3.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.19/3.43  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 3.19/3.43      inference('sup-', [status(thm)], ['122', '123'])).
% 3.19/3.43  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 3.19/3.43      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.19/3.43  thf('127', plain,
% 3.19/3.43      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (sk_A))
% 3.19/3.43        | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['112', '121', '124', '125', '126'])).
% 3.19/3.43  thf('128', plain,
% 3.19/3.43      ((((sk_A) = (k1_xboole_0)) | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 3.19/3.43      inference('clc', [status(thm)], ['84', '127'])).
% 3.19/3.43  thf('129', plain,
% 3.19/3.43      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('clc', [status(thm)], ['62', '128'])).
% 3.19/3.43  thf('130', plain,
% 3.19/3.43      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 3.19/3.43      inference('demod', [status(thm)], ['19', '20'])).
% 3.19/3.43  thf('131', plain,
% 3.19/3.43      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['129', '130'])).
% 3.19/3.43  thf('132', plain,
% 3.19/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('133', plain,
% 3.19/3.43      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.19/3.43      inference('simplify', [status(thm)], ['47'])).
% 3.19/3.43  thf('134', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 3.19/3.43      inference('sup-', [status(thm)], ['132', '133'])).
% 3.19/3.43  thf('135', plain, (((sk_A) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['131', '134'])).
% 3.19/3.43  thf('136', plain, (((sk_A) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['131', '134'])).
% 3.19/3.43  thf('137', plain,
% 3.19/3.43      ((r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B_1) @ sk_C @ k1_xboole_0) @ 
% 3.19/3.43        k1_xboole_0)),
% 3.19/3.43      inference('demod', [status(thm)], ['22', '135', '136'])).
% 3.19/3.43  thf(rc2_subset_1, axiom,
% 3.19/3.43    (![A:$i]:
% 3.19/3.43     ( ?[B:$i]:
% 3.19/3.43       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 3.19/3.43  thf('138', plain, (![X3 : $i]: (v1_xboole_0 @ (sk_B @ X3))),
% 3.19/3.43      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.19/3.43  thf(t4_subset_1, axiom,
% 3.19/3.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.19/3.43  thf('139', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf(dt_k1_relset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.43       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.19/3.43  thf('140', plain,
% 3.19/3.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 3.19/3.43          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 3.19/3.43  thf('141', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 3.19/3.43          (k1_zfmisc_1 @ X1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['139', '140'])).
% 3.19/3.43  thf(cc1_subset_1, axiom,
% 3.19/3.43    (![A:$i]:
% 3.19/3.43     ( ( v1_xboole_0 @ A ) =>
% 3.19/3.43       ( ![B:$i]:
% 3.19/3.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.19/3.43  thf('142', plain,
% 3.19/3.43      (![X5 : $i, X6 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.19/3.43          | (v1_xboole_0 @ X5)
% 3.19/3.43          | ~ (v1_xboole_0 @ X6))),
% 3.19/3.43      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.19/3.43  thf('143', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0)
% 3.19/3.43          | (v1_xboole_0 @ (k1_relset_1 @ X0 @ X1 @ k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['141', '142'])).
% 3.19/3.43  thf('144', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf('145', plain,
% 3.19/3.43      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.19/3.43         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.19/3.43          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.19/3.43  thf('146', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['144', '145'])).
% 3.19/3.43  thf('147', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['143', '146'])).
% 3.19/3.43  thf('148', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['138', '147'])).
% 3.19/3.43  thf('149', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('150', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf('151', plain,
% 3.19/3.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 3.19/3.43          | (r2_relset_1 @ X31 @ X31 @ X32 @ X30)
% 3.19/3.43          | (r2_hidden @ (sk_D @ X30 @ X32 @ X31) @ X31)
% 3.19/3.43          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31))))),
% 3.19/3.43      inference('cnf', [status(esa)], [t54_relset_1])).
% 3.19/3.43  thf('152', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 3.19/3.43          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.19/3.43          | (r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['150', '151'])).
% 3.19/3.43  thf('153', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ k1_xboole_0)
% 3.19/3.43          | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k6_partfun1 @ X0) @ X0) @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['149', '152'])).
% 3.19/3.43  thf('154', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf(t5_subset, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.19/3.43          ( v1_xboole_0 @ C ) ) ))).
% 3.19/3.43  thf('155', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         (~ (r2_hidden @ X10 @ X11)
% 3.19/3.43          | ~ (v1_xboole_0 @ X12)
% 3.19/3.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t5_subset])).
% 3.19/3.43  thf('156', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['154', '155'])).
% 3.19/3.43  thf('157', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.19/3.43           (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)
% 3.19/3.43          | ~ (v1_xboole_0 @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['153', '156'])).
% 3.19/3.43  thf('158', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf('159', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('160', plain,
% 3.19/3.43      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ((X26) = (X29))
% 3.19/3.43          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.19/3.43  thf('161', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 3.19/3.43          | ((k6_partfun1 @ X0) = (X1))
% 3.19/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['159', '160'])).
% 3.19/3.43  thf('162', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((k6_partfun1 @ X0) = (k1_xboole_0))
% 3.19/3.43          | ~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['158', '161'])).
% 3.19/3.43  thf('163', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['157', '162'])).
% 3.19/3.43  thf('164', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['148', '163'])).
% 3.19/3.43  thf('165', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('166', plain,
% 3.19/3.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 3.19/3.43          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 3.19/3.43  thf('167', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k1_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0)) @ 
% 3.19/3.43          (k1_zfmisc_1 @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['165', '166'])).
% 3.19/3.43  thf('168', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         (~ (r2_hidden @ X10 @ X11)
% 3.19/3.43          | ~ (v1_xboole_0 @ X12)
% 3.19/3.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t5_subset])).
% 3.19/3.43  thf('169', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0)
% 3.19/3.43          | ~ (r2_hidden @ X1 @ (k1_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['167', '168'])).
% 3.19/3.43  thf('170', plain,
% 3.19/3.43      (![X45 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.19/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.43  thf('171', plain,
% 3.19/3.43      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.19/3.43         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.19/3.43          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.19/3.43  thf('172', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k1_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0))
% 3.19/3.43           = (k1_relat_1 @ (k6_partfun1 @ X0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['170', '171'])).
% 3.19/3.43  thf('173', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (v1_xboole_0 @ X0)
% 3.19/3.43          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))),
% 3.19/3.43      inference('demod', [status(thm)], ['169', '172'])).
% 3.19/3.43  thf('174', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (~ (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 3.19/3.43          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['164', '173'])).
% 3.19/3.43  thf('175', plain, (![X3 : $i]: (v1_xboole_0 @ (sk_B @ X3))),
% 3.19/3.43      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.19/3.43  thf('176', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf('177', plain,
% 3.19/3.43      (![X5 : $i, X6 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.19/3.43          | (v1_xboole_0 @ X5)
% 3.19/3.43          | ~ (v1_xboole_0 @ X6))),
% 3.19/3.43      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.19/3.43  thf('178', plain,
% 3.19/3.43      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['176', '177'])).
% 3.19/3.43  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.43      inference('sup-', [status(thm)], ['175', '178'])).
% 3.19/3.43  thf('180', plain,
% 3.19/3.43      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['174', '179'])).
% 3.19/3.43  thf('181', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 3.19/3.43          (k1_zfmisc_1 @ X1))),
% 3.19/3.43      inference('sup-', [status(thm)], ['139', '140'])).
% 3.19/3.43  thf('182', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['144', '145'])).
% 3.19/3.43  thf('183', plain,
% 3.19/3.43      (![X1 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X1))),
% 3.19/3.43      inference('demod', [status(thm)], ['181', '182'])).
% 3.19/3.43  thf('184', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 3.19/3.43          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.19/3.43          | (r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['150', '151'])).
% 3.19/3.43  thf('185', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((r2_relset_1 @ X0 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 3.19/3.43          | (r2_hidden @ 
% 3.19/3.43             (sk_D @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0) @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['183', '184'])).
% 3.19/3.43  thf('186', plain,
% 3.19/3.43      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['174', '179'])).
% 3.19/3.43  thf('187', plain,
% 3.19/3.43      ((r2_relset_1 @ (k1_relat_1 @ k1_xboole_0) @ 
% 3.19/3.43        (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 3.19/3.43      inference('sup-', [status(thm)], ['185', '186'])).
% 3.19/3.43  thf('188', plain,
% 3.19/3.43      (![X1 : $i]:
% 3.19/3.43         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X1))),
% 3.19/3.43      inference('demod', [status(thm)], ['181', '182'])).
% 3.19/3.43  thf('189', plain,
% 3.19/3.43      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.19/3.43         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.19/3.43          | ((X26) = (X29))
% 3.19/3.43          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 3.19/3.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.19/3.43  thf('190', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         (~ (r2_relset_1 @ X1 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ X2)
% 3.19/3.43          | ((k1_relat_1 @ k1_xboole_0) = (X2))
% 3.19/3.43          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['188', '189'])).
% 3.19/3.43  thf('191', plain,
% 3.19/3.43      ((~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.19/3.43           (k1_zfmisc_1 @ 
% 3.19/3.43            (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ 
% 3.19/3.43             (k1_relat_1 @ k1_xboole_0))))
% 3.19/3.43        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['187', '190'])).
% 3.19/3.43  thf('192', plain,
% 3.19/3.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.19/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.19/3.43  thf('193', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['191', '192'])).
% 3.19/3.43  thf('194', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.19/3.43      inference('demod', [status(thm)], ['180', '193'])).
% 3.19/3.43  thf('195', plain, ($false), inference('sup-', [status(thm)], ['137', '194'])).
% 3.19/3.43  
% 3.19/3.43  % SZS output end Refutation
% 3.19/3.43  
% 3.19/3.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
