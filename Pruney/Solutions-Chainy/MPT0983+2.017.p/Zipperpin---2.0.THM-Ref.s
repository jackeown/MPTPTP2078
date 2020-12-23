%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DMJdxjo2ky

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:03 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 473 expanded)
%              Number of leaves         :   45 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          : 1215 (9210 expanded)
%              Number of equality atoms :   36 ( 107 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('6',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('13',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('29',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('34',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','43','46','47','48','49'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('51',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('52',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','43','46','47','48','49'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['53','56','57','60'])).

thf('62',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('63',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('65',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['15','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('78',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86','87','88','89'])).

thf('91',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('92',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('93',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['90','93'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','94','96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['66','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DMJdxjo2ky
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.78/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/1.03  % Solved by: fo/fo7.sh
% 0.78/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.03  % done 1000 iterations in 0.567s
% 0.78/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/1.03  % SZS output start Refutation
% 0.78/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.78/1.03  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.78/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.78/1.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.78/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.78/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.78/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.78/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/1.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.78/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.78/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.78/1.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.78/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.78/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.78/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.78/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/1.03  thf(d3_tarski, axiom,
% 0.78/1.03    (![A:$i,B:$i]:
% 0.78/1.03     ( ( r1_tarski @ A @ B ) <=>
% 0.78/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.78/1.03  thf('0', plain,
% 0.78/1.03      (![X4 : $i, X6 : $i]:
% 0.78/1.03         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.78/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/1.03  thf(d1_xboole_0, axiom,
% 0.78/1.03    (![A:$i]:
% 0.78/1.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.78/1.03  thf('1', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.78/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/1.03  thf('2', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.78/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/1.03  thf(t3_subset, axiom,
% 0.78/1.03    (![A:$i,B:$i]:
% 0.78/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/1.03  thf('3', plain,
% 0.78/1.03      (![X10 : $i, X12 : $i]:
% 0.78/1.03         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.78/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.03  thf('4', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]:
% 0.78/1.03         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.78/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/1.03  thf(cc1_relset_1, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i]:
% 0.78/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/1.03       ( v1_relat_1 @ C ) ))).
% 0.78/1.03  thf('5', plain,
% 0.78/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.78/1.03         ((v1_relat_1 @ X17)
% 0.78/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.78/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.78/1.03  thf('6', plain, (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ X2))),
% 0.78/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.78/1.03  thf(cc1_funct_1, axiom,
% 0.78/1.03    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.78/1.03  thf('7', plain, (![X13 : $i]: ((v1_funct_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.78/1.03      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.78/1.03  thf(cc2_funct_1, axiom,
% 0.78/1.03    (![A:$i]:
% 0.78/1.03     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/1.03       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.78/1.03  thf('8', plain,
% 0.78/1.03      (![X14 : $i]:
% 0.78/1.03         ((v2_funct_1 @ X14)
% 0.78/1.03          | ~ (v1_funct_1 @ X14)
% 0.78/1.03          | ~ (v1_relat_1 @ X14)
% 0.78/1.03          | ~ (v1_xboole_0 @ X14))),
% 0.78/1.03      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.78/1.03  thf('9', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (~ (v1_xboole_0 @ X0)
% 0.78/1.03          | ~ (v1_xboole_0 @ X0)
% 0.78/1.03          | ~ (v1_relat_1 @ X0)
% 0.78/1.03          | (v2_funct_1 @ X0))),
% 0.78/1.03      inference('sup-', [status(thm)], ['7', '8'])).
% 0.78/1.03  thf('10', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.78/1.03      inference('simplify', [status(thm)], ['9'])).
% 0.78/1.03  thf('11', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.78/1.03      inference('sup-', [status(thm)], ['6', '10'])).
% 0.78/1.03  thf('12', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.78/1.03      inference('simplify', [status(thm)], ['11'])).
% 0.78/1.03  thf(t29_funct_2, conjecture,
% 0.78/1.03    (![A:$i,B:$i,C:$i]:
% 0.78/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.78/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.03       ( ![D:$i]:
% 0.78/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.78/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.78/1.03           ( ( r2_relset_1 @
% 0.78/1.03               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.78/1.03               ( k6_partfun1 @ A ) ) =>
% 0.78/1.03             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.78/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.78/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.78/1.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.78/1.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.03          ( ![D:$i]:
% 0.78/1.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.78/1.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.78/1.03              ( ( r2_relset_1 @
% 0.78/1.03                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.78/1.03                  ( k6_partfun1 @ A ) ) =>
% 0.78/1.03                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.78/1.03    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.78/1.03  thf('13', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('14', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 0.78/1.03      inference('split', [status(esa)], ['13'])).
% 0.78/1.03  thf('15', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 0.78/1.03      inference('sup-', [status(thm)], ['12', '14'])).
% 0.78/1.03  thf('16', plain,
% 0.78/1.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.78/1.03        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.78/1.03        (k6_partfun1 @ sk_A))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('17', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('18', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf(dt_k1_partfun1, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.78/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.78/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.78/1.03         ( v1_funct_1 @ F ) & 
% 0.78/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.78/1.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.78/1.03         ( m1_subset_1 @
% 0.78/1.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.78/1.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.78/1.03  thf('19', plain,
% 0.78/1.03      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.78/1.03         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.78/1.03          | ~ (v1_funct_1 @ X33)
% 0.78/1.03          | ~ (v1_funct_1 @ X36)
% 0.78/1.03          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.78/1.03          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 0.78/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 0.78/1.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.78/1.03  thf('20', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.03         ((m1_subset_1 @ 
% 0.78/1.03           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.78/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.78/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.78/1.03          | ~ (v1_funct_1 @ X1)
% 0.78/1.03          | ~ (v1_funct_1 @ sk_C_1))),
% 0.78/1.03      inference('sup-', [status(thm)], ['18', '19'])).
% 0.78/1.03  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('22', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.03         ((m1_subset_1 @ 
% 0.78/1.03           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.78/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.78/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.78/1.03          | ~ (v1_funct_1 @ X1))),
% 0.78/1.03      inference('demod', [status(thm)], ['20', '21'])).
% 0.78/1.03  thf('23', plain,
% 0.78/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.78/1.03        | (m1_subset_1 @ 
% 0.78/1.03           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.78/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.78/1.03      inference('sup-', [status(thm)], ['17', '22'])).
% 0.78/1.03  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('25', plain,
% 0.78/1.03      ((m1_subset_1 @ 
% 0.78/1.03        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.78/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.78/1.03      inference('demod', [status(thm)], ['23', '24'])).
% 0.78/1.03  thf(redefinition_r2_relset_1, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.78/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.78/1.03  thf('26', plain,
% 0.78/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.78/1.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.78/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.78/1.03          | ((X26) = (X29))
% 0.78/1.03          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 0.78/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.78/1.03  thf('27', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.78/1.03             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 0.78/1.03          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 0.78/1.03              = (X0))
% 0.78/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.78/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.78/1.03  thf('28', plain,
% 0.78/1.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.78/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.78/1.03        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 0.78/1.03            = (k6_partfun1 @ sk_A)))),
% 0.78/1.03      inference('sup-', [status(thm)], ['16', '27'])).
% 0.78/1.03  thf(t29_relset_1, axiom,
% 0.78/1.03    (![A:$i]:
% 0.78/1.03     ( m1_subset_1 @
% 0.78/1.03       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.78/1.03  thf('29', plain,
% 0.78/1.03      (![X30 : $i]:
% 0.78/1.03         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.78/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.78/1.03      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.78/1.03  thf(redefinition_k6_partfun1, axiom,
% 0.78/1.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.78/1.03  thf('30', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.78/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.78/1.03  thf('31', plain,
% 0.78/1.03      (![X30 : $i]:
% 0.78/1.03         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.78/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.78/1.03      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/1.03  thf('32', plain,
% 0.78/1.03      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 0.78/1.03         = (k6_partfun1 @ sk_A))),
% 0.78/1.03      inference('demod', [status(thm)], ['28', '31'])).
% 0.78/1.03  thf('33', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf(t24_funct_2, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i]:
% 0.78/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.78/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.03       ( ![D:$i]:
% 0.78/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.78/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.78/1.03           ( ( r2_relset_1 @
% 0.78/1.03               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.78/1.03               ( k6_partfun1 @ B ) ) =>
% 0.78/1.03             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.78/1.03  thf('34', plain,
% 0.78/1.03      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X40)
% 0.78/1.03          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.78/1.03          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.78/1.03          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 0.78/1.03               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 0.78/1.03               (k6_partfun1 @ X41))
% 0.78/1.03          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 0.78/1.03          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.78/1.03          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.78/1.03          | ~ (v1_funct_1 @ X43))),
% 0.78/1.03      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.78/1.03  thf('35', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X0)
% 0.78/1.03          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.78/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.78/1.03          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.78/1.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.78/1.03               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 0.78/1.03               (k6_partfun1 @ sk_A))
% 0.78/1.03          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.78/1.03          | ~ (v1_funct_1 @ sk_C_1))),
% 0.78/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/1.03  thf('36', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('38', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X0)
% 0.78/1.03          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.78/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.78/1.03          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.78/1.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.78/1.03               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 0.78/1.03               (k6_partfun1 @ sk_A)))),
% 0.78/1.03      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.78/1.03  thf('39', plain,
% 0.78/1.03      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.78/1.03           (k6_partfun1 @ sk_A))
% 0.78/1.03        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.78/1.03        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.78/1.03        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.78/1.03        | ~ (v1_funct_1 @ sk_D))),
% 0.78/1.03      inference('sup-', [status(thm)], ['32', '38'])).
% 0.78/1.03  thf('40', plain,
% 0.78/1.03      (![X30 : $i]:
% 0.78/1.03         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.78/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.78/1.03      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/1.03  thf('41', plain,
% 0.78/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.78/1.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.78/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.78/1.03          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 0.78/1.03          | ((X26) != (X29)))),
% 0.78/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.78/1.03  thf('42', plain,
% 0.78/1.03      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/1.03         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 0.78/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.78/1.03      inference('simplify', [status(thm)], ['41'])).
% 0.78/1.03  thf('43', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.78/1.03      inference('sup-', [status(thm)], ['40', '42'])).
% 0.78/1.03  thf('44', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf(redefinition_k2_relset_1, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i]:
% 0.78/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/1.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.78/1.03  thf('45', plain,
% 0.78/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.78/1.03         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.78/1.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.78/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.78/1.03  thf('46', plain,
% 0.78/1.03      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.78/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.78/1.03  thf('47', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('50', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.78/1.03      inference('demod', [status(thm)], ['39', '43', '46', '47', '48', '49'])).
% 0.78/1.03  thf(d3_funct_2, axiom,
% 0.78/1.03    (![A:$i,B:$i]:
% 0.78/1.03     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.78/1.03       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.78/1.03  thf('51', plain,
% 0.78/1.03      (![X31 : $i, X32 : $i]:
% 0.78/1.03         (((k2_relat_1 @ X32) != (X31))
% 0.78/1.03          | (v2_funct_2 @ X32 @ X31)
% 0.78/1.03          | ~ (v5_relat_1 @ X32 @ X31)
% 0.78/1.03          | ~ (v1_relat_1 @ X32))),
% 0.78/1.03      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.78/1.03  thf('52', plain,
% 0.78/1.03      (![X32 : $i]:
% 0.78/1.03         (~ (v1_relat_1 @ X32)
% 0.78/1.03          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 0.78/1.03          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 0.78/1.03      inference('simplify', [status(thm)], ['51'])).
% 0.78/1.03  thf('53', plain,
% 0.78/1.03      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.78/1.03        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.78/1.03        | ~ (v1_relat_1 @ sk_D))),
% 0.78/1.03      inference('sup-', [status(thm)], ['50', '52'])).
% 0.78/1.03  thf('54', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf(cc2_relset_1, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i]:
% 0.78/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/1.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.78/1.03  thf('55', plain,
% 0.78/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/1.03         ((v5_relat_1 @ X20 @ X22)
% 0.78/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.78/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.78/1.03  thf('56', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.78/1.03      inference('sup-', [status(thm)], ['54', '55'])).
% 0.78/1.03  thf('57', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.78/1.03      inference('demod', [status(thm)], ['39', '43', '46', '47', '48', '49'])).
% 0.78/1.03  thf('58', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('59', plain,
% 0.78/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.78/1.03         ((v1_relat_1 @ X17)
% 0.78/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.78/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.78/1.03  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.78/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.78/1.03  thf('61', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.78/1.03      inference('demod', [status(thm)], ['53', '56', '57', '60'])).
% 0.78/1.03  thf('62', plain,
% 0.78/1.03      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.78/1.03      inference('split', [status(esa)], ['13'])).
% 0.78/1.03  thf('63', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.78/1.03      inference('sup-', [status(thm)], ['61', '62'])).
% 0.78/1.03  thf('64', plain,
% 0.78/1.03      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.78/1.03      inference('split', [status(esa)], ['13'])).
% 0.78/1.03  thf('65', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 0.78/1.03      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.78/1.03  thf('66', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.78/1.03      inference('simpl_trail', [status(thm)], ['15', '65'])).
% 0.78/1.03  thf('67', plain,
% 0.78/1.03      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.78/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/1.03  thf('68', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('69', plain,
% 0.78/1.03      (![X10 : $i, X11 : $i]:
% 0.78/1.03         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.78/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.03  thf('70', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.78/1.03      inference('sup-', [status(thm)], ['68', '69'])).
% 0.78/1.03  thf('71', plain,
% 0.78/1.03      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.78/1.03         (~ (r2_hidden @ X3 @ X4)
% 0.78/1.03          | (r2_hidden @ X3 @ X5)
% 0.78/1.03          | ~ (r1_tarski @ X4 @ X5))),
% 0.78/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/1.03  thf('72', plain,
% 0.78/1.03      (![X0 : $i]:
% 0.78/1.03         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.78/1.03          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.78/1.03      inference('sup-', [status(thm)], ['70', '71'])).
% 0.78/1.03  thf('73', plain,
% 0.78/1.03      (((v1_xboole_0 @ sk_C_1)
% 0.78/1.03        | (r2_hidden @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('sup-', [status(thm)], ['67', '72'])).
% 0.78/1.03  thf('74', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.78/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/1.03  thf('75', plain,
% 0.78/1.03      (((v1_xboole_0 @ sk_C_1)
% 0.78/1.03        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('sup-', [status(thm)], ['73', '74'])).
% 0.78/1.03  thf('76', plain,
% 0.78/1.03      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 0.78/1.03         = (k6_partfun1 @ sk_A))),
% 0.78/1.03      inference('demod', [status(thm)], ['28', '31'])).
% 0.78/1.03  thf('77', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf(t26_funct_2, axiom,
% 0.78/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.78/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.03       ( ![E:$i]:
% 0.78/1.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.78/1.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.78/1.03           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.78/1.03             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.78/1.03               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.78/1.03  thf('78', plain,
% 0.78/1.03      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X44)
% 0.78/1.03          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.78/1.03          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.78/1.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 0.78/1.03          | (v2_funct_1 @ X48)
% 0.78/1.03          | ((X46) = (k1_xboole_0))
% 0.78/1.03          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.78/1.03          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 0.78/1.03          | ~ (v1_funct_1 @ X48))),
% 0.78/1.03      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.78/1.03  thf('79', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X0)
% 0.78/1.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.78/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.78/1.03          | ((sk_A) = (k1_xboole_0))
% 0.78/1.03          | (v2_funct_1 @ X0)
% 0.78/1.03          | ~ (v2_funct_1 @ 
% 0.78/1.03               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.78/1.03          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.78/1.03          | ~ (v1_funct_1 @ sk_D))),
% 0.78/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.78/1.03  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('82', plain,
% 0.78/1.03      (![X0 : $i, X1 : $i]:
% 0.78/1.03         (~ (v1_funct_1 @ X0)
% 0.78/1.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.78/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.78/1.03          | ((sk_A) = (k1_xboole_0))
% 0.78/1.03          | (v2_funct_1 @ X0)
% 0.78/1.03          | ~ (v2_funct_1 @ 
% 0.78/1.03               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.78/1.03      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.78/1.03  thf('83', plain,
% 0.78/1.03      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.78/1.03        | (v2_funct_1 @ sk_C_1)
% 0.78/1.03        | ((sk_A) = (k1_xboole_0))
% 0.78/1.03        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.78/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.78/1.03        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.78/1.03        | ~ (v1_funct_1 @ sk_C_1))),
% 0.78/1.03      inference('sup-', [status(thm)], ['76', '82'])).
% 0.78/1.03  thf(fc4_funct_1, axiom,
% 0.78/1.03    (![A:$i]:
% 0.78/1.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.78/1.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.78/1.03  thf('84', plain, (![X16 : $i]: (v2_funct_1 @ (k6_relat_1 @ X16))),
% 0.78/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.78/1.03  thf('85', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.78/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.78/1.03  thf('86', plain, (![X16 : $i]: (v2_funct_1 @ (k6_partfun1 @ X16))),
% 0.78/1.03      inference('demod', [status(thm)], ['84', '85'])).
% 0.78/1.03  thf('87', plain,
% 0.78/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('88', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('89', plain, ((v1_funct_1 @ sk_C_1)),
% 0.78/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.03  thf('90', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 0.78/1.03      inference('demod', [status(thm)], ['83', '86', '87', '88', '89'])).
% 0.78/1.03  thf('91', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 0.78/1.03      inference('split', [status(esa)], ['13'])).
% 0.78/1.03  thf('92', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 0.78/1.03      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.78/1.03  thf('93', plain, (~ (v2_funct_1 @ sk_C_1)),
% 0.78/1.03      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.78/1.03  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 0.78/1.03      inference('clc', [status(thm)], ['90', '93'])).
% 0.78/1.03  thf(t113_zfmisc_1, axiom,
% 0.78/1.03    (![A:$i,B:$i]:
% 0.78/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.78/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.78/1.03  thf('95', plain,
% 0.78/1.03      (![X8 : $i, X9 : $i]:
% 0.78/1.03         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.78/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.78/1.03  thf('96', plain,
% 0.78/1.03      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.78/1.03      inference('simplify', [status(thm)], ['95'])).
% 0.78/1.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.78/1.03  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/1.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/1.03  thf('98', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.78/1.03      inference('demod', [status(thm)], ['75', '94', '96', '97'])).
% 0.78/1.03  thf('99', plain, ($false), inference('demod', [status(thm)], ['66', '98'])).
% 0.78/1.03  
% 0.78/1.03  % SZS output end Refutation
% 0.78/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
