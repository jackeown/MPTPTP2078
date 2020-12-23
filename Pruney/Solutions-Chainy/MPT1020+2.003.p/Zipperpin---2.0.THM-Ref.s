%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDEqrxyc9X

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:01 EST 2020

% Result     : Theorem 16.72s
% Output     : Refutation 16.72s
% Verified   : 
% Statistics : Number of formulae       :  176 (1678 expanded)
%              Number of leaves         :   53 ( 521 expanded)
%              Depth                    :   14
%              Number of atoms          : 1340 (39476 expanded)
%              Number of equality atoms :   97 ( 758 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_funct_2 @ X43 @ X42 )
        = ( k2_funct_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
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

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_partfun1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('14',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( X49
        = ( k2_funct_1 @ X52 ) )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_relat_1 @ X51 ) )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X39 )
      | ( v2_funct_2 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('30',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v2_funct_2 @ X41 @ X40 )
      | ( ( k2_relat_1 @ X41 )
        = X40 )
      | ~ ( v5_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['27','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X39 )
      | ( v2_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','45','51'])).

thf('53',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('55',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('62',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X17 ) @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('65',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('70',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc17_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc17_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('73',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) @ X15 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('82',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','94'])).

thf('96',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['65','66','67','69','70','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X17 ) @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('99',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('101',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('103',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','94'])).

thf('105',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('106',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X18: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X18 ) )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('108',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('110',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','96','105','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('114',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('116',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('117',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('119',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('120',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['111','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDEqrxyc9X
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.72/16.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.72/16.90  % Solved by: fo/fo7.sh
% 16.72/16.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.72/16.90  % done 7182 iterations in 16.441s
% 16.72/16.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.72/16.90  % SZS output start Refutation
% 16.72/16.90  thf(sk_A_type, type, sk_A: $i).
% 16.72/16.90  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 16.72/16.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.72/16.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.72/16.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 16.72/16.90  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 16.72/16.90  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 16.72/16.90  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 16.72/16.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.72/16.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 16.72/16.90  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 16.72/16.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.72/16.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 16.72/16.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.72/16.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 16.72/16.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 16.72/16.90  thf(sk_B_type, type, sk_B: $i > $i).
% 16.72/16.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 16.72/16.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.72/16.90  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 16.72/16.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.72/16.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 16.72/16.90  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 16.72/16.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 16.72/16.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.72/16.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 16.72/16.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 16.72/16.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 16.72/16.90  thf(sk_C_type, type, sk_C: $i).
% 16.72/16.90  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 16.72/16.90  thf(t87_funct_2, conjecture,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.72/16.90         ( v3_funct_2 @ B @ A @ A ) & 
% 16.72/16.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.72/16.90       ( ![C:$i]:
% 16.72/16.90         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 16.72/16.90             ( v3_funct_2 @ C @ A @ A ) & 
% 16.72/16.90             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.72/16.90           ( ( r2_relset_1 @
% 16.72/16.90               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 16.72/16.90               ( k6_partfun1 @ A ) ) =>
% 16.72/16.90             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 16.72/16.90  thf(zf_stmt_0, negated_conjecture,
% 16.72/16.90    (~( ![A:$i,B:$i]:
% 16.72/16.90        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.72/16.90            ( v3_funct_2 @ B @ A @ A ) & 
% 16.72/16.90            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.72/16.90          ( ![C:$i]:
% 16.72/16.90            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 16.72/16.90                ( v3_funct_2 @ C @ A @ A ) & 
% 16.72/16.90                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.72/16.90              ( ( r2_relset_1 @
% 16.72/16.90                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 16.72/16.90                  ( k6_partfun1 @ A ) ) =>
% 16.72/16.90                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 16.72/16.90    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 16.72/16.90  thf('0', plain,
% 16.72/16.90      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('1', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(redefinition_k2_funct_2, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 16.72/16.90         ( v3_funct_2 @ B @ A @ A ) & 
% 16.72/16.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 16.72/16.90       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 16.72/16.90  thf('2', plain,
% 16.72/16.90      (![X42 : $i, X43 : $i]:
% 16.72/16.90         (((k2_funct_2 @ X43 @ X42) = (k2_funct_1 @ X42))
% 16.72/16.90          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))
% 16.72/16.90          | ~ (v3_funct_2 @ X42 @ X43 @ X43)
% 16.72/16.90          | ~ (v1_funct_2 @ X42 @ X43 @ X43)
% 16.72/16.90          | ~ (v1_funct_1 @ X42))),
% 16.72/16.90      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 16.72/16.90  thf('3', plain,
% 16.72/16.90      ((~ (v1_funct_1 @ sk_B_1)
% 16.72/16.90        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 16.72/16.90        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 16.72/16.90        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['1', '2'])).
% 16.72/16.90  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('6', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 16.72/16.90  thf('8', plain,
% 16.72/16.90      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)], ['0', '7'])).
% 16.72/16.90  thf('9', plain,
% 16.72/16.90      ((r2_relset_1 @ sk_A @ sk_A @ 
% 16.72/16.90        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 16.72/16.90        (k6_partfun1 @ sk_A))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(redefinition_k6_partfun1, axiom,
% 16.72/16.90    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 16.72/16.90  thf('10', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 16.72/16.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 16.72/16.90  thf('11', plain,
% 16.72/16.90      ((r2_relset_1 @ sk_A @ sk_A @ 
% 16.72/16.90        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 16.72/16.90        (k6_relat_1 @ sk_A))),
% 16.72/16.90      inference('demod', [status(thm)], ['9', '10'])).
% 16.72/16.90  thf('12', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(t36_funct_2, axiom,
% 16.72/16.90    (![A:$i,B:$i,C:$i]:
% 16.72/16.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 16.72/16.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.72/16.90       ( ![D:$i]:
% 16.72/16.90         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 16.72/16.90             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 16.72/16.90           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 16.72/16.90               ( r2_relset_1 @
% 16.72/16.90                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 16.72/16.90                 ( k6_partfun1 @ A ) ) & 
% 16.72/16.90               ( v2_funct_1 @ C ) ) =>
% 16.72/16.90             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 16.72/16.90               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 16.72/16.90  thf('13', plain,
% 16.72/16.90      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X49)
% 16.72/16.90          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 16.72/16.90          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 16.72/16.90          | ((X49) = (k2_funct_1 @ X52))
% 16.72/16.90          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 16.72/16.90               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 16.72/16.90               (k6_partfun1 @ X51))
% 16.72/16.90          | ((X50) = (k1_xboole_0))
% 16.72/16.90          | ((X51) = (k1_xboole_0))
% 16.72/16.90          | ~ (v2_funct_1 @ X52)
% 16.72/16.90          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 16.72/16.90          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 16.72/16.90          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 16.72/16.90          | ~ (v1_funct_1 @ X52))),
% 16.72/16.90      inference('cnf', [status(esa)], [t36_funct_2])).
% 16.72/16.90  thf('14', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 16.72/16.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 16.72/16.90  thf('15', plain,
% 16.72/16.90      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X49)
% 16.72/16.90          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 16.72/16.90          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 16.72/16.90          | ((X49) = (k2_funct_1 @ X52))
% 16.72/16.90          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 16.72/16.90               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 16.72/16.90               (k6_relat_1 @ X51))
% 16.72/16.90          | ((X50) = (k1_xboole_0))
% 16.72/16.90          | ((X51) = (k1_xboole_0))
% 16.72/16.90          | ~ (v2_funct_1 @ X52)
% 16.72/16.90          | ((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 16.72/16.90          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 16.72/16.90          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 16.72/16.90          | ~ (v1_funct_1 @ X52))),
% 16.72/16.90      inference('demod', [status(thm)], ['13', '14'])).
% 16.72/16.90  thf('16', plain,
% 16.72/16.90      (![X0 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X0)
% 16.72/16.90          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 16.72/16.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 16.72/16.90          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 16.72/16.90          | ~ (v2_funct_1 @ X0)
% 16.72/16.90          | ((sk_A) = (k1_xboole_0))
% 16.72/16.90          | ((sk_A) = (k1_xboole_0))
% 16.72/16.90          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 16.72/16.90               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 16.72/16.90               (k6_relat_1 @ sk_A))
% 16.72/16.90          | ((sk_C) = (k2_funct_1 @ X0))
% 16.72/16.90          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 16.72/16.90          | ~ (v1_funct_1 @ sk_C))),
% 16.72/16.90      inference('sup-', [status(thm)], ['12', '15'])).
% 16.72/16.90  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('19', plain,
% 16.72/16.90      (![X0 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X0)
% 16.72/16.90          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 16.72/16.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 16.72/16.90          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 16.72/16.90          | ~ (v2_funct_1 @ X0)
% 16.72/16.90          | ((sk_A) = (k1_xboole_0))
% 16.72/16.90          | ((sk_A) = (k1_xboole_0))
% 16.72/16.90          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 16.72/16.90               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 16.72/16.90               (k6_relat_1 @ sk_A))
% 16.72/16.90          | ((sk_C) = (k2_funct_1 @ X0)))),
% 16.72/16.90      inference('demod', [status(thm)], ['16', '17', '18'])).
% 16.72/16.90  thf('20', plain,
% 16.72/16.90      (![X0 : $i]:
% 16.72/16.90         (((sk_C) = (k2_funct_1 @ X0))
% 16.72/16.90          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 16.72/16.90               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 16.72/16.90               (k6_relat_1 @ sk_A))
% 16.72/16.90          | ((sk_A) = (k1_xboole_0))
% 16.72/16.90          | ~ (v2_funct_1 @ X0)
% 16.72/16.90          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 16.72/16.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 16.72/16.90          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 16.72/16.90          | ~ (v1_funct_1 @ X0))),
% 16.72/16.90      inference('simplify', [status(thm)], ['19'])).
% 16.72/16.90  thf('21', plain,
% 16.72/16.90      ((~ (v1_funct_1 @ sk_B_1)
% 16.72/16.90        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 16.72/16.90        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 16.72/16.90        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 16.72/16.90        | ~ (v2_funct_1 @ sk_B_1)
% 16.72/16.90        | ((sk_A) = (k1_xboole_0))
% 16.72/16.90        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['11', '20'])).
% 16.72/16.90  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('23', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('24', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('25', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(redefinition_k2_relset_1, axiom,
% 16.72/16.90    (![A:$i,B:$i,C:$i]:
% 16.72/16.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.72/16.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 16.72/16.90  thf('26', plain,
% 16.72/16.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 16.72/16.90         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 16.72/16.90          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 16.72/16.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 16.72/16.90  thf('27', plain,
% 16.72/16.90      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 16.72/16.90      inference('sup-', [status(thm)], ['25', '26'])).
% 16.72/16.90  thf('28', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(cc2_funct_2, axiom,
% 16.72/16.90    (![A:$i,B:$i,C:$i]:
% 16.72/16.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.72/16.90       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 16.72/16.90         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 16.72/16.90  thf('29', plain,
% 16.72/16.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X37)
% 16.72/16.90          | ~ (v3_funct_2 @ X37 @ X38 @ X39)
% 16.72/16.90          | (v2_funct_2 @ X37 @ X39)
% 16.72/16.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc2_funct_2])).
% 16.72/16.90  thf('30', plain,
% 16.72/16.90      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 16.72/16.90        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 16.72/16.90        | ~ (v1_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('sup-', [status(thm)], ['28', '29'])).
% 16.72/16.90  thf('31', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('32', plain, ((v1_funct_1 @ sk_B_1)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('33', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 16.72/16.90      inference('demod', [status(thm)], ['30', '31', '32'])).
% 16.72/16.90  thf(d3_funct_2, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 16.72/16.90       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 16.72/16.90  thf('34', plain,
% 16.72/16.90      (![X40 : $i, X41 : $i]:
% 16.72/16.90         (~ (v2_funct_2 @ X41 @ X40)
% 16.72/16.90          | ((k2_relat_1 @ X41) = (X40))
% 16.72/16.90          | ~ (v5_relat_1 @ X41 @ X40)
% 16.72/16.90          | ~ (v1_relat_1 @ X41))),
% 16.72/16.90      inference('cnf', [status(esa)], [d3_funct_2])).
% 16.72/16.90  thf('35', plain,
% 16.72/16.90      ((~ (v1_relat_1 @ sk_B_1)
% 16.72/16.90        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 16.72/16.90        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['33', '34'])).
% 16.72/16.90  thf('36', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(cc2_relat_1, axiom,
% 16.72/16.90    (![A:$i]:
% 16.72/16.90     ( ( v1_relat_1 @ A ) =>
% 16.72/16.90       ( ![B:$i]:
% 16.72/16.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 16.72/16.90  thf('37', plain,
% 16.72/16.90      (![X6 : $i, X7 : $i]:
% 16.72/16.90         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 16.72/16.90          | (v1_relat_1 @ X6)
% 16.72/16.90          | ~ (v1_relat_1 @ X7))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 16.72/16.90  thf('38', plain,
% 16.72/16.90      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 16.72/16.90      inference('sup-', [status(thm)], ['36', '37'])).
% 16.72/16.90  thf(fc6_relat_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 16.72/16.90  thf('39', plain,
% 16.72/16.90      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 16.72/16.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 16.72/16.90  thf('40', plain, ((v1_relat_1 @ sk_B_1)),
% 16.72/16.90      inference('demod', [status(thm)], ['38', '39'])).
% 16.72/16.90  thf('41', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(cc2_relset_1, axiom,
% 16.72/16.90    (![A:$i,B:$i,C:$i]:
% 16.72/16.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.72/16.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 16.72/16.90  thf('42', plain,
% 16.72/16.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 16.72/16.90         ((v5_relat_1 @ X21 @ X23)
% 16.72/16.90          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.72/16.90  thf('43', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 16.72/16.90      inference('sup-', [status(thm)], ['41', '42'])).
% 16.72/16.90  thf('44', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 16.72/16.90      inference('demod', [status(thm)], ['35', '40', '43'])).
% 16.72/16.90  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 16.72/16.90      inference('demod', [status(thm)], ['27', '44'])).
% 16.72/16.90  thf('46', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('47', plain,
% 16.72/16.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.72/16.90         (~ (v1_funct_1 @ X37)
% 16.72/16.90          | ~ (v3_funct_2 @ X37 @ X38 @ X39)
% 16.72/16.90          | (v2_funct_1 @ X37)
% 16.72/16.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc2_funct_2])).
% 16.72/16.90  thf('48', plain,
% 16.72/16.90      (((v2_funct_1 @ sk_B_1)
% 16.72/16.90        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 16.72/16.90        | ~ (v1_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('sup-', [status(thm)], ['46', '47'])).
% 16.72/16.90  thf('49', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('51', plain, ((v2_funct_1 @ sk_B_1)),
% 16.72/16.90      inference('demod', [status(thm)], ['48', '49', '50'])).
% 16.72/16.90  thf('52', plain,
% 16.72/16.90      ((((sk_A) != (sk_A))
% 16.72/16.90        | ((sk_A) = (k1_xboole_0))
% 16.72/16.90        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 16.72/16.90      inference('demod', [status(thm)], ['21', '22', '23', '24', '45', '51'])).
% 16.72/16.90  thf('53', plain,
% 16.72/16.90      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 16.72/16.90      inference('simplify', [status(thm)], ['52'])).
% 16.72/16.90  thf('54', plain,
% 16.72/16.90      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)], ['0', '7'])).
% 16.72/16.90  thf('55', plain,
% 16.72/16.90      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['53', '54'])).
% 16.72/16.90  thf('56', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(redefinition_r2_relset_1, axiom,
% 16.72/16.90    (![A:$i,B:$i,C:$i,D:$i]:
% 16.72/16.90     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 16.72/16.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.72/16.90       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 16.72/16.90  thf('57', plain,
% 16.72/16.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 16.72/16.90         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 16.72/16.90          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 16.72/16.90          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 16.72/16.90          | ((X27) != (X30)))),
% 16.72/16.90      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 16.72/16.90  thf('58', plain,
% 16.72/16.90      (![X28 : $i, X29 : $i, X30 : $i]:
% 16.72/16.90         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 16.72/16.90          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 16.72/16.90      inference('simplify', [status(thm)], ['57'])).
% 16.72/16.90  thf('59', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 16.72/16.90      inference('sup-', [status(thm)], ['56', '58'])).
% 16.72/16.90  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('62', plain,
% 16.72/16.90      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 16.72/16.90          (k2_funct_1 @ sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)], ['8', '60', '61'])).
% 16.72/16.90  thf('63', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf(t162_funct_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.72/16.90       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 16.72/16.90  thf('64', plain,
% 16.72/16.90      (![X16 : $i, X17 : $i]:
% 16.72/16.90         (((k9_relat_1 @ (k6_relat_1 @ X17) @ X16) = (X16))
% 16.72/16.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 16.72/16.90      inference('cnf', [status(esa)], [t162_funct_1])).
% 16.72/16.90  thf('65', plain,
% 16.72/16.90      (((k9_relat_1 @ (k6_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) @ sk_C)
% 16.72/16.90         = (sk_C))),
% 16.72/16.90      inference('sup-', [status(thm)], ['63', '64'])).
% 16.72/16.90  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf(t113_zfmisc_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 16.72/16.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 16.72/16.90  thf('68', plain,
% 16.72/16.90      (![X3 : $i, X4 : $i]:
% 16.72/16.90         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 16.72/16.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 16.72/16.90  thf('69', plain,
% 16.72/16.90      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 16.72/16.90      inference('simplify', [status(thm)], ['68'])).
% 16.72/16.90  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 16.72/16.90  thf('70', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('cnf', [status(esa)], [t81_relat_1])).
% 16.72/16.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 16.72/16.90  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 16.72/16.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 16.72/16.90  thf(fc17_relat_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) ) =>
% 16.72/16.90       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 16.72/16.90         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 16.72/16.90  thf('72', plain,
% 16.72/16.90      (![X8 : $i, X9 : $i]:
% 16.72/16.90         (~ (v1_relat_1 @ X8)
% 16.72/16.90          | ~ (v1_xboole_0 @ X8)
% 16.72/16.90          | (v1_xboole_0 @ (k7_relat_1 @ X8 @ X9)))),
% 16.72/16.90      inference('cnf', [status(esa)], [fc17_relat_1])).
% 16.72/16.90  thf(cc1_relat_1, axiom,
% 16.72/16.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 16.72/16.90  thf('73', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc1_relat_1])).
% 16.72/16.90  thf('74', plain,
% 16.72/16.90      (![X8 : $i, X9 : $i]:
% 16.72/16.90         ((v1_xboole_0 @ (k7_relat_1 @ X8 @ X9)) | ~ (v1_xboole_0 @ X8))),
% 16.72/16.90      inference('clc', [status(thm)], ['72', '73'])).
% 16.72/16.90  thf(t148_relat_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ( v1_relat_1 @ B ) =>
% 16.72/16.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 16.72/16.90  thf('75', plain,
% 16.72/16.90      (![X12 : $i, X13 : $i]:
% 16.72/16.90         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 16.72/16.90          | ~ (v1_relat_1 @ X12))),
% 16.72/16.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 16.72/16.90  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 16.72/16.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 16.72/16.90  thf(t8_boole, axiom,
% 16.72/16.90    (![A:$i,B:$i]:
% 16.72/16.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 16.72/16.90  thf('77', plain,
% 16.72/16.90      (![X0 : $i, X1 : $i]:
% 16.72/16.90         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 16.72/16.90      inference('cnf', [status(esa)], [t8_boole])).
% 16.72/16.90  thf('78', plain,
% 16.72/16.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup-', [status(thm)], ['76', '77'])).
% 16.72/16.90  thf('79', plain,
% 16.72/16.90      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 16.72/16.90      inference('simplify', [status(thm)], ['68'])).
% 16.72/16.90  thf(t194_relat_1, axiom,
% 16.72/16.90    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 16.72/16.90  thf('80', plain,
% 16.72/16.90      (![X14 : $i, X15 : $i]:
% 16.72/16.90         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X14 @ X15)) @ X15)),
% 16.72/16.90      inference('cnf', [status(esa)], [t194_relat_1])).
% 16.72/16.90  thf('81', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 16.72/16.90      inference('sup+', [status(thm)], ['79', '80'])).
% 16.72/16.90  thf(t6_mcart_1, axiom,
% 16.72/16.90    (![A:$i]:
% 16.72/16.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 16.72/16.90          ( ![B:$i]:
% 16.72/16.90            ( ~( ( r2_hidden @ B @ A ) & 
% 16.72/16.90                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 16.72/16.90                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 16.72/16.90                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 16.72/16.90                       ( r2_hidden @ G @ B ) ) =>
% 16.72/16.90                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 16.72/16.90  thf('82', plain,
% 16.72/16.90      (![X31 : $i]:
% 16.72/16.90         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X31) @ X31))),
% 16.72/16.90      inference('cnf', [status(esa)], [t6_mcart_1])).
% 16.72/16.90  thf(t7_ordinal1, axiom,
% 16.72/16.90    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.72/16.90  thf('83', plain,
% 16.72/16.90      (![X19 : $i, X20 : $i]:
% 16.72/16.90         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 16.72/16.90      inference('cnf', [status(esa)], [t7_ordinal1])).
% 16.72/16.90  thf('84', plain,
% 16.72/16.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['82', '83'])).
% 16.72/16.90  thf('85', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('sup-', [status(thm)], ['81', '84'])).
% 16.72/16.90  thf('86', plain,
% 16.72/16.90      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup+', [status(thm)], ['78', '85'])).
% 16.72/16.90  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 16.72/16.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 16.72/16.90  thf('88', plain,
% 16.72/16.90      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup+', [status(thm)], ['86', '87'])).
% 16.72/16.90  thf('89', plain,
% 16.72/16.90      (![X0 : $i, X1 : $i]:
% 16.72/16.90         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 16.72/16.90          | ~ (v1_relat_1 @ X1)
% 16.72/16.90          | ~ (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0)))),
% 16.72/16.90      inference('sup+', [status(thm)], ['75', '88'])).
% 16.72/16.90  thf('90', plain,
% 16.72/16.90      (![X0 : $i, X1 : $i]:
% 16.72/16.90         (~ (v1_xboole_0 @ X1)
% 16.72/16.90          | ~ (v1_relat_1 @ X1)
% 16.72/16.90          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['74', '89'])).
% 16.72/16.90  thf('91', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 16.72/16.90      inference('cnf', [status(esa)], [cc1_relat_1])).
% 16.72/16.90  thf('92', plain,
% 16.72/16.90      (![X0 : $i, X1 : $i]:
% 16.72/16.90         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 16.72/16.90      inference('clc', [status(thm)], ['90', '91'])).
% 16.72/16.90  thf('93', plain,
% 16.72/16.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup-', [status(thm)], ['76', '77'])).
% 16.72/16.90  thf('94', plain,
% 16.72/16.90      (![X0 : $i, X1 : $i]:
% 16.72/16.90         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k9_relat_1 @ X1 @ X0)))),
% 16.72/16.90      inference('sup-', [status(thm)], ['92', '93'])).
% 16.72/16.90  thf('95', plain,
% 16.72/16.90      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup-', [status(thm)], ['71', '94'])).
% 16.72/16.90  thf('96', plain, (((k1_xboole_0) = (sk_C))),
% 16.72/16.90      inference('demod', [status(thm)], ['65', '66', '67', '69', '70', '95'])).
% 16.72/16.90  thf('97', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('98', plain,
% 16.72/16.90      (![X16 : $i, X17 : $i]:
% 16.72/16.90         (((k9_relat_1 @ (k6_relat_1 @ X17) @ X16) = (X16))
% 16.72/16.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 16.72/16.90      inference('cnf', [status(esa)], [t162_funct_1])).
% 16.72/16.90  thf('99', plain,
% 16.72/16.90      (((k9_relat_1 @ (k6_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) @ sk_B_1)
% 16.72/16.90         = (sk_B_1))),
% 16.72/16.90      inference('sup-', [status(thm)], ['97', '98'])).
% 16.72/16.90  thf('100', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('101', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('102', plain,
% 16.72/16.90      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 16.72/16.90      inference('simplify', [status(thm)], ['68'])).
% 16.72/16.90  thf('103', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('cnf', [status(esa)], [t81_relat_1])).
% 16.72/16.90  thf('104', plain,
% 16.72/16.90      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 16.72/16.90      inference('sup-', [status(thm)], ['71', '94'])).
% 16.72/16.90  thf('105', plain, (((k1_xboole_0) = (sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)],
% 16.72/16.90                ['99', '100', '101', '102', '103', '104'])).
% 16.72/16.90  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('cnf', [status(esa)], [t81_relat_1])).
% 16.72/16.90  thf(t67_funct_1, axiom,
% 16.72/16.90    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 16.72/16.90  thf('107', plain,
% 16.72/16.90      (![X18 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X18)) = (k6_relat_1 @ X18))),
% 16.72/16.90      inference('cnf', [status(esa)], [t67_funct_1])).
% 16.72/16.90  thf('108', plain,
% 16.72/16.90      (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 16.72/16.90      inference('sup+', [status(thm)], ['106', '107'])).
% 16.72/16.90  thf('109', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('cnf', [status(esa)], [t81_relat_1])).
% 16.72/16.90  thf('110', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.72/16.90      inference('sup+', [status(thm)], ['108', '109'])).
% 16.72/16.90  thf('111', plain,
% 16.72/16.90      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 16.72/16.90      inference('demod', [status(thm)], ['62', '96', '105', '110'])).
% 16.72/16.90  thf('112', plain,
% 16.72/16.90      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 16.72/16.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.72/16.90  thf('113', plain,
% 16.72/16.90      (![X28 : $i, X29 : $i, X30 : $i]:
% 16.72/16.90         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 16.72/16.90          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 16.72/16.90      inference('simplify', [status(thm)], ['57'])).
% 16.72/16.90  thf('114', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 16.72/16.90      inference('sup-', [status(thm)], ['112', '113'])).
% 16.72/16.90  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('116', plain, (((sk_A) = (k1_xboole_0))),
% 16.72/16.90      inference('demod', [status(thm)], ['55', '59'])).
% 16.72/16.90  thf('117', plain,
% 16.72/16.90      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1)),
% 16.72/16.90      inference('demod', [status(thm)], ['114', '115', '116'])).
% 16.72/16.90  thf('118', plain, (((k1_xboole_0) = (sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)],
% 16.72/16.90                ['99', '100', '101', '102', '103', '104'])).
% 16.72/16.90  thf('119', plain, (((k1_xboole_0) = (sk_B_1))),
% 16.72/16.90      inference('demod', [status(thm)],
% 16.72/16.90                ['99', '100', '101', '102', '103', '104'])).
% 16.72/16.90  thf('120', plain,
% 16.72/16.90      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 16.72/16.90      inference('demod', [status(thm)], ['117', '118', '119'])).
% 16.72/16.90  thf('121', plain, ($false), inference('demod', [status(thm)], ['111', '120'])).
% 16.72/16.90  
% 16.72/16.90  % SZS output end Refutation
% 16.72/16.90  
% 16.72/16.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
