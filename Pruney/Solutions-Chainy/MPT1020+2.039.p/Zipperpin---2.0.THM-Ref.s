%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1OXPwmKQSj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:07 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 925 expanded)
%              Number of leaves         :   40 ( 288 expanded)
%              Depth                    :   15
%              Number of atoms          : 1328 (23003 expanded)
%              Number of equality atoms :  103 ( 390 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k2_funct_2 @ X24 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30
        = ( k2_funct_1 @ X33 ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30 ) @ ( k6_partfun1 @ X32 ) )
      | ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30
        = ( k2_funct_1 @ X33 ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30 ) @ ( k6_relat_1 @ X32 ) )
      | ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('30',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['27','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','43','49'])).

thf('51',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('53',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('63',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['68','71','74'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('77',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('79',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','38','41'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('92',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('102',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_funct_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('107',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('108',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('109',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('110',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('114',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['60','82','90','107','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1OXPwmKQSj
% 0.15/0.38  % Computer   : n005.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:49:48 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 164 iterations in 0.080s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.37/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.37/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.37/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(t87_funct_2, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.57         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57       ( ![C:$i]:
% 0.37/0.57         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.57             ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.57             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57           ( ( r2_relset_1 @
% 0.37/0.57               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.37/0.57               ( k6_partfun1 @ A ) ) =>
% 0.37/0.57             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.57            ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.57            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57          ( ![C:$i]:
% 0.37/0.57            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.57                ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.57                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57              ( ( r2_relset_1 @
% 0.37/0.57                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.37/0.57                  ( k6_partfun1 @ A ) ) =>
% 0.37/0.57                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k2_funct_2, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.57         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i]:
% 0.37/0.57         (((k2_funct_2 @ X24 @ X23) = (k2_funct_1 @ X23))
% 0.37/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.37/0.57          | ~ (v3_funct_2 @ X23 @ X24 @ X24)
% 0.37/0.57          | ~ (v1_funct_2 @ X23 @ X24 @ X24)
% 0.37/0.57          | ~ (v1_funct_1 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.37/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.57        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.37/0.57  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.57        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.37/0.57        (k6_partfun1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.37/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.37/0.57  thf('10', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.57        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.37/0.57        (k6_relat_1 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t36_funct_2, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57       ( ![D:$i]:
% 0.37/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.37/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.37/0.57           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.37/0.57               ( r2_relset_1 @
% 0.37/0.57                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.37/0.57                 ( k6_partfun1 @ A ) ) & 
% 0.37/0.57               ( v2_funct_1 @ C ) ) =>
% 0.37/0.57             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X30)
% 0.37/0.57          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.37/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.37/0.57          | ((X30) = (k2_funct_1 @ X33))
% 0.37/0.57          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.37/0.57               (k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30) @ 
% 0.37/0.57               (k6_partfun1 @ X32))
% 0.37/0.57          | ((X31) = (k1_xboole_0))
% 0.37/0.57          | ((X32) = (k1_xboole_0))
% 0.37/0.57          | ~ (v2_funct_1 @ X33)
% 0.37/0.57          | ((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.37/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.37/0.57          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.37/0.57          | ~ (v1_funct_1 @ X33))),
% 0.37/0.57      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.37/0.57  thf('14', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X30)
% 0.37/0.57          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.37/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.37/0.57          | ((X30) = (k2_funct_1 @ X33))
% 0.37/0.57          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.37/0.57               (k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30) @ 
% 0.37/0.57               (k6_relat_1 @ X32))
% 0.37/0.57          | ((X31) = (k1_xboole_0))
% 0.37/0.57          | ((X32) = (k1_xboole_0))
% 0.37/0.57          | ~ (v2_funct_1 @ X33)
% 0.37/0.57          | ((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.37/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.37/0.57          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.37/0.57          | ~ (v1_funct_1 @ X33))),
% 0.37/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ((sk_A) = (k1_xboole_0))
% 0.37/0.57          | ((sk_A) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.57               (k6_relat_1 @ sk_A))
% 0.37/0.57          | ((sk_C) = (k2_funct_1 @ X0))
% 0.37/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.57  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ((sk_A) = (k1_xboole_0))
% 0.37/0.57          | ((sk_A) = (k1_xboole_0))
% 0.37/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.57               (k6_relat_1 @ sk_A))
% 0.37/0.57          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((sk_C) = (k2_funct_1 @ X0))
% 0.37/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.57               (k6_relat_1 @ sk_A))
% 0.37/0.57          | ((sk_A) = (k1_xboole_0))
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.57          | ~ (v1_funct_1 @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.37/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.57        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.57        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.37/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.37/0.57        | ((sk_A) = (k1_xboole_0))
% 0.37/0.57        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '20'])).
% 0.37/0.57  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('23', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.57         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.37/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc2_funct_2, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.57         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X16)
% 0.37/0.57          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.37/0.57          | (v2_funct_2 @ X16 @ X18)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (((v2_funct_2 @ sk_B @ sk_A)
% 0.37/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.57  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.37/0.57  thf(d3_funct_2, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.37/0.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i]:
% 0.37/0.57         (~ (v2_funct_2 @ X20 @ X19)
% 0.37/0.57          | ((k2_relat_1 @ X20) = (X19))
% 0.37/0.57          | ~ (v5_relat_1 @ X20 @ X19)
% 0.37/0.57          | ~ (v1_relat_1 @ X20))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.37/0.57        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.37/0.57        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc1_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( v1_relat_1 @ C ) ))).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.57         ((v1_relat_1 @ X3)
% 0.37/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.57  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc2_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         ((v5_relat_1 @ X6 @ X8)
% 0.37/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.57  thf('41', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.37/0.57  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['27', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X16)
% 0.37/0.57          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.37/0.57          | (v2_funct_1 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (((v2_funct_1 @ sk_B)
% 0.37/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      ((((sk_A) != (sk_A))
% 0.37/0.57        | ((sk_A) = (k1_xboole_0))
% 0.37/0.57        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['21', '22', '23', '24', '43', '49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.37/0.57          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.37/0.57          | ((X12) != (X15)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.57  thf('57', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.37/0.57      inference('sup-', [status(thm)], ['54', '56'])).
% 0.37/0.57  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '57'])).
% 0.37/0.57  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '57'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['8', '58', '59'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (v1_funct_1 @ X16)
% 0.37/0.57          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.37/0.57          | (v2_funct_2 @ X16 @ X18)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (((v2_funct_2 @ sk_C @ sk_A)
% 0.37/0.57        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.57  thf('64', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('66', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i]:
% 0.37/0.57         (~ (v2_funct_2 @ X20 @ X19)
% 0.37/0.57          | ((k2_relat_1 @ X20) = (X19))
% 0.37/0.57          | ~ (v5_relat_1 @ X20 @ X19)
% 0.37/0.57          | ~ (v1_relat_1 @ X20))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.57        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.37/0.57        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('70', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.57         ((v1_relat_1 @ X3)
% 0.37/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.57  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         ((v5_relat_1 @ X6 @ X8)
% 0.37/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.57  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.57  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['68', '71', '74'])).
% 0.37/0.57  thf(t64_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.57          | ((X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      ((((sk_A) != (k1_xboole_0))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.57        | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.57  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.57  thf('79', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.37/0.57  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '57'])).
% 0.37/0.57  thf('81', plain,
% 0.37/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.57  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['81'])).
% 0.37/0.57  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.57          | ((X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.57  thf('85', plain,
% 0.37/0.57      ((((sk_A) != (k1_xboole_0))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.37/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['83', '84'])).
% 0.37/0.57  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('87', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['85', '86'])).
% 0.37/0.57  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '57'])).
% 0.37/0.57  thf('89', plain,
% 0.37/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.57  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.37/0.57  thf('91', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.37/0.57  thf(fc6_funct_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.37/0.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.57         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.57  thf('92', plain,
% 0.37/0.57      (![X1 : $i]:
% 0.37/0.57         ((v1_relat_1 @ (k2_funct_1 @ X1))
% 0.37/0.57          | ~ (v2_funct_1 @ X1)
% 0.37/0.57          | ~ (v1_funct_1 @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.37/0.57  thf(t55_funct_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.57       ( ( v2_funct_1 @ A ) =>
% 0.37/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.37/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('93', plain,
% 0.37/0.57      (![X2 : $i]:
% 0.37/0.57         (~ (v2_funct_1 @ X2)
% 0.37/0.57          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.37/0.57          | ~ (v1_funct_1 @ X2)
% 0.37/0.57          | ~ (v1_relat_1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.57  thf('94', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.57          | ((X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.57  thf('95', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.57          | ~ (v1_relat_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.37/0.57          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['93', '94'])).
% 0.37/0.57  thf('96', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X0)
% 0.37/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['92', '95'])).
% 0.37/0.57  thf('97', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.57          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 0.37/0.57          | ~ (v2_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['96'])).
% 0.37/0.57  thf('98', plain,
% 0.37/0.57      ((((sk_A) != (k1_xboole_0))
% 0.37/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.37/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.37/0.57        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['91', '97'])).
% 0.37/0.57  thf('99', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('101', plain, ((v2_funct_1 @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.37/0.57  thf('102', plain,
% 0.37/0.57      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.37/0.57  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '57'])).
% 0.37/0.57  thf('104', plain,
% 0.37/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.57        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['102', '103'])).
% 0.37/0.57  thf('105', plain, (((k2_funct_1 @ sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['104'])).
% 0.37/0.57  thf('106', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.37/0.57  thf('107', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.57  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.57  thf('108', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.37/0.57  thf(dt_k6_partfun1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( m1_subset_1 @
% 0.37/0.57         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.37/0.57       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.37/0.57  thf('109', plain,
% 0.37/0.57      (![X22 : $i]:
% 0.37/0.57         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.37/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.37/0.57  thf('110', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.57  thf('111', plain,
% 0.37/0.57      (![X22 : $i]:
% 0.37/0.57         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.37/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.37/0.57      inference('demod', [status(thm)], ['109', '110'])).
% 0.37/0.57  thf('112', plain,
% 0.37/0.57      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['108', '111'])).
% 0.37/0.57  thf('113', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.57  thf('114', plain,
% 0.37/0.57      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.37/0.57  thf('115', plain, ($false),
% 0.37/0.57      inference('demod', [status(thm)], ['60', '82', '90', '107', '114'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
