%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OD24qCv0B2

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:10 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  157 (1207 expanded)
%              Number of leaves         :   40 ( 375 expanded)
%              Depth                    :   15
%              Number of atoms          : 1210 (28923 expanded)
%              Number of equality atoms :   74 ( 454 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_2 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['27','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','45','51'])).

thf('53',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_2 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('65',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['70','75','78'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('100',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('101',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('102',plain,(
    ! [X7: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X7 ) )
      = ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('103',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('105',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('108',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('110',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('111',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('113',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('114',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['62','90','100','105','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OD24qCv0B2
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.64/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.86  % Solved by: fo/fo7.sh
% 1.64/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.86  % done 1634 iterations in 1.410s
% 1.64/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.86  % SZS output start Refutation
% 1.64/1.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.64/1.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.64/1.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.64/1.86  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.64/1.86  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.64/1.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.64/1.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.64/1.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.64/1.86  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.64/1.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.64/1.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.64/1.86  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.64/1.86  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.64/1.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.64/1.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.64/1.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.64/1.86  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.64/1.86  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.64/1.86  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.86  thf(sk_C_type, type, sk_C: $i).
% 1.64/1.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.86  thf(t87_funct_2, conjecture,
% 1.64/1.86    (![A:$i,B:$i]:
% 1.64/1.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.64/1.86         ( v3_funct_2 @ B @ A @ A ) & 
% 1.64/1.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.64/1.86       ( ![C:$i]:
% 1.64/1.86         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.64/1.86             ( v3_funct_2 @ C @ A @ A ) & 
% 1.64/1.86             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.64/1.86           ( ( r2_relset_1 @
% 1.64/1.86               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.64/1.86               ( k6_partfun1 @ A ) ) =>
% 1.64/1.86             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 1.64/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.86    (~( ![A:$i,B:$i]:
% 1.64/1.86        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.64/1.86            ( v3_funct_2 @ B @ A @ A ) & 
% 1.64/1.86            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.64/1.86          ( ![C:$i]:
% 1.64/1.86            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.64/1.86                ( v3_funct_2 @ C @ A @ A ) & 
% 1.64/1.86                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.64/1.86              ( ( r2_relset_1 @
% 1.64/1.86                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.64/1.86                  ( k6_partfun1 @ A ) ) =>
% 1.64/1.86                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 1.64/1.86    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 1.64/1.86  thf('0', plain,
% 1.64/1.86      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.64/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.86  thf('1', plain,
% 1.64/1.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.86  thf(redefinition_k2_funct_2, axiom,
% 1.64/1.86    (![A:$i,B:$i]:
% 1.64/1.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.64/1.86         ( v3_funct_2 @ B @ A @ A ) & 
% 1.64/1.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.64/1.86       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.64/1.86  thf('2', plain,
% 1.64/1.86      (![X23 : $i, X24 : $i]:
% 1.64/1.86         (((k2_funct_2 @ X24 @ X23) = (k2_funct_1 @ X23))
% 1.64/1.86          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 1.64/1.86          | ~ (v3_funct_2 @ X23 @ X24 @ X24)
% 1.64/1.86          | ~ (v1_funct_2 @ X23 @ X24 @ X24)
% 1.64/1.86          | ~ (v1_funct_1 @ X23))),
% 1.64/1.86      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.64/1.86  thf('3', plain,
% 1.64/1.86      ((~ (v1_funct_1 @ sk_B)
% 1.64/1.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.64/1.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.64/1.86        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.64/1.86      inference('sup-', [status(thm)], ['1', '2'])).
% 1.64/1.86  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 1.64/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.64/1.87      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 1.64/1.87  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.64/1.87      inference('demod', [status(thm)], ['0', '7'])).
% 1.64/1.87  thf('9', plain,
% 1.64/1.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.64/1.87        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 1.64/1.87        (k6_partfun1 @ sk_A))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(redefinition_k6_partfun1, axiom,
% 1.64/1.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.64/1.87  thf('10', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.64/1.87  thf('11', plain,
% 1.64/1.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.64/1.87        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 1.64/1.87        (k6_relat_1 @ sk_A))),
% 1.64/1.87      inference('demod', [status(thm)], ['9', '10'])).
% 1.64/1.87  thf('12', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(t36_funct_2, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.64/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.64/1.87       ( ![D:$i]:
% 1.64/1.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.64/1.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.64/1.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.64/1.87               ( r2_relset_1 @
% 1.64/1.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.64/1.87                 ( k6_partfun1 @ A ) ) & 
% 1.64/1.87               ( v2_funct_1 @ C ) ) =>
% 1.64/1.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.64/1.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.64/1.87  thf('13', plain,
% 1.64/1.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X30)
% 1.64/1.87          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 1.64/1.87          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.64/1.87          | ((X30) = (k2_funct_1 @ X33))
% 1.64/1.87          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.64/1.87               (k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30) @ 
% 1.64/1.87               (k6_partfun1 @ X32))
% 1.64/1.87          | ((X31) = (k1_xboole_0))
% 1.64/1.87          | ((X32) = (k1_xboole_0))
% 1.64/1.87          | ~ (v2_funct_1 @ X33)
% 1.64/1.87          | ((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 1.64/1.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.64/1.87          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 1.64/1.87          | ~ (v1_funct_1 @ X33))),
% 1.64/1.87      inference('cnf', [status(esa)], [t36_funct_2])).
% 1.64/1.87  thf('14', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.64/1.87  thf('15', plain,
% 1.64/1.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X30)
% 1.64/1.87          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 1.64/1.87          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.64/1.87          | ((X30) = (k2_funct_1 @ X33))
% 1.64/1.87          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.64/1.87               (k1_partfun1 @ X32 @ X31 @ X31 @ X32 @ X33 @ X30) @ 
% 1.64/1.87               (k6_relat_1 @ X32))
% 1.64/1.87          | ((X31) = (k1_xboole_0))
% 1.64/1.87          | ((X32) = (k1_xboole_0))
% 1.64/1.87          | ~ (v2_funct_1 @ X33)
% 1.64/1.87          | ((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 1.64/1.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.64/1.87          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 1.64/1.87          | ~ (v1_funct_1 @ X33))),
% 1.64/1.87      inference('demod', [status(thm)], ['13', '14'])).
% 1.64/1.87  thf('16', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X0)
% 1.64/1.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.64/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.64/1.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.64/1.87          | ~ (v2_funct_1 @ X0)
% 1.64/1.87          | ((sk_A) = (k1_xboole_0))
% 1.64/1.87          | ((sk_A) = (k1_xboole_0))
% 1.64/1.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.64/1.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.64/1.87               (k6_relat_1 @ sk_A))
% 1.64/1.87          | ((sk_C) = (k2_funct_1 @ X0))
% 1.64/1.87          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.64/1.87          | ~ (v1_funct_1 @ sk_C))),
% 1.64/1.87      inference('sup-', [status(thm)], ['12', '15'])).
% 1.64/1.87  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('19', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X0)
% 1.64/1.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.64/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.64/1.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.64/1.87          | ~ (v2_funct_1 @ X0)
% 1.64/1.87          | ((sk_A) = (k1_xboole_0))
% 1.64/1.87          | ((sk_A) = (k1_xboole_0))
% 1.64/1.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.64/1.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.64/1.87               (k6_relat_1 @ sk_A))
% 1.64/1.87          | ((sk_C) = (k2_funct_1 @ X0)))),
% 1.64/1.87      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.64/1.87  thf('20', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (((sk_C) = (k2_funct_1 @ X0))
% 1.64/1.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.64/1.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.64/1.87               (k6_relat_1 @ sk_A))
% 1.64/1.87          | ((sk_A) = (k1_xboole_0))
% 1.64/1.87          | ~ (v2_funct_1 @ X0)
% 1.64/1.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.64/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.64/1.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.64/1.87          | ~ (v1_funct_1 @ X0))),
% 1.64/1.87      inference('simplify', [status(thm)], ['19'])).
% 1.64/1.87  thf('21', plain,
% 1.64/1.87      ((~ (v1_funct_1 @ sk_B)
% 1.64/1.87        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.64/1.87        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.64/1.87        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 1.64/1.87        | ~ (v2_funct_1 @ sk_B)
% 1.64/1.87        | ((sk_A) = (k1_xboole_0))
% 1.64/1.87        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['11', '20'])).
% 1.64/1.87  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('23', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('24', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('25', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(redefinition_k2_relset_1, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.64/1.87  thf('26', plain,
% 1.64/1.87      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.64/1.87         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.64/1.87          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.64/1.87  thf('27', plain,
% 1.64/1.87      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['25', '26'])).
% 1.64/1.87  thf('28', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(cc2_funct_2, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.87       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.64/1.87         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.64/1.87  thf('29', plain,
% 1.64/1.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X18)
% 1.64/1.87          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 1.64/1.87          | (v2_funct_2 @ X18 @ X20)
% 1.64/1.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.64/1.87  thf('30', plain,
% 1.64/1.87      (((v2_funct_2 @ sk_B @ sk_A)
% 1.64/1.87        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.64/1.87        | ~ (v1_funct_1 @ sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['28', '29'])).
% 1.64/1.87  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('33', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.64/1.87      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.64/1.87  thf(d3_funct_2, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.64/1.87       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.64/1.87  thf('34', plain,
% 1.64/1.87      (![X21 : $i, X22 : $i]:
% 1.64/1.87         (~ (v2_funct_2 @ X22 @ X21)
% 1.64/1.87          | ((k2_relat_1 @ X22) = (X21))
% 1.64/1.87          | ~ (v5_relat_1 @ X22 @ X21)
% 1.64/1.87          | ~ (v1_relat_1 @ X22))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.64/1.87  thf('35', plain,
% 1.64/1.87      ((~ (v1_relat_1 @ sk_B)
% 1.64/1.87        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.64/1.87        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['33', '34'])).
% 1.64/1.87  thf('36', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(cc2_relat_1, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( v1_relat_1 @ A ) =>
% 1.64/1.87       ( ![B:$i]:
% 1.64/1.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.64/1.87  thf('37', plain,
% 1.64/1.87      (![X2 : $i, X3 : $i]:
% 1.64/1.87         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.64/1.87          | (v1_relat_1 @ X2)
% 1.64/1.87          | ~ (v1_relat_1 @ X3))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.64/1.87  thf('38', plain,
% 1.64/1.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['36', '37'])).
% 1.64/1.87  thf(fc6_relat_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.64/1.87  thf('39', plain,
% 1.64/1.87      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.64/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.64/1.87  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.64/1.87      inference('demod', [status(thm)], ['38', '39'])).
% 1.64/1.87  thf('41', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(cc2_relset_1, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.64/1.87  thf('42', plain,
% 1.64/1.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.64/1.87         ((v5_relat_1 @ X8 @ X10)
% 1.64/1.87          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.64/1.87  thf('43', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.64/1.87      inference('sup-', [status(thm)], ['41', '42'])).
% 1.64/1.87  thf('44', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.64/1.87      inference('demod', [status(thm)], ['35', '40', '43'])).
% 1.64/1.87  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 1.64/1.87      inference('demod', [status(thm)], ['27', '44'])).
% 1.64/1.87  thf('46', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('47', plain,
% 1.64/1.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X18)
% 1.64/1.87          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 1.64/1.87          | (v2_funct_1 @ X18)
% 1.64/1.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.64/1.87  thf('48', plain,
% 1.64/1.87      (((v2_funct_1 @ sk_B)
% 1.64/1.87        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.64/1.87        | ~ (v1_funct_1 @ sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['46', '47'])).
% 1.64/1.87  thf('49', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('51', plain, ((v2_funct_1 @ sk_B)),
% 1.64/1.87      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.64/1.87  thf('52', plain,
% 1.64/1.87      ((((sk_A) != (sk_A))
% 1.64/1.87        | ((sk_A) = (k1_xboole_0))
% 1.64/1.87        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 1.64/1.87      inference('demod', [status(thm)], ['21', '22', '23', '24', '45', '51'])).
% 1.64/1.87  thf('53', plain,
% 1.64/1.87      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['52'])).
% 1.64/1.87  thf('54', plain,
% 1.64/1.87      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.64/1.87      inference('demod', [status(thm)], ['0', '7'])).
% 1.64/1.87  thf('55', plain,
% 1.64/1.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['53', '54'])).
% 1.64/1.87  thf('56', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(redefinition_r2_relset_1, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.64/1.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.64/1.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.64/1.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.64/1.87  thf('57', plain,
% 1.64/1.87      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.64/1.87         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.64/1.87          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.64/1.87          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 1.64/1.87          | ((X14) != (X17)))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.64/1.87  thf('58', plain,
% 1.64/1.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.64/1.87         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 1.64/1.87          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['57'])).
% 1.64/1.87  thf('59', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.64/1.87      inference('sup-', [status(thm)], ['56', '58'])).
% 1.64/1.87  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf('62', plain,
% 1.64/1.87      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.64/1.87      inference('demod', [status(thm)], ['8', '60', '61'])).
% 1.64/1.87  thf('63', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('64', plain,
% 1.64/1.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.64/1.87         (~ (v1_funct_1 @ X18)
% 1.64/1.87          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 1.64/1.87          | (v2_funct_2 @ X18 @ X20)
% 1.64/1.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.64/1.87  thf('65', plain,
% 1.64/1.87      (((v2_funct_2 @ sk_C @ sk_A)
% 1.64/1.87        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.64/1.87        | ~ (v1_funct_1 @ sk_C))),
% 1.64/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.64/1.87  thf('66', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('68', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 1.64/1.87      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.64/1.87  thf('69', plain,
% 1.64/1.87      (![X21 : $i, X22 : $i]:
% 1.64/1.87         (~ (v2_funct_2 @ X22 @ X21)
% 1.64/1.87          | ((k2_relat_1 @ X22) = (X21))
% 1.64/1.87          | ~ (v5_relat_1 @ X22 @ X21)
% 1.64/1.87          | ~ (v1_relat_1 @ X22))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.64/1.87  thf('70', plain,
% 1.64/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.64/1.87        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 1.64/1.87        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['68', '69'])).
% 1.64/1.87  thf('71', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('72', plain,
% 1.64/1.87      (![X2 : $i, X3 : $i]:
% 1.64/1.87         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.64/1.87          | (v1_relat_1 @ X2)
% 1.64/1.87          | ~ (v1_relat_1 @ X3))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.64/1.87  thf('73', plain,
% 1.64/1.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 1.64/1.87      inference('sup-', [status(thm)], ['71', '72'])).
% 1.64/1.87  thf('74', plain,
% 1.64/1.87      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.64/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.64/1.87  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.87      inference('demod', [status(thm)], ['73', '74'])).
% 1.64/1.87  thf('76', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('77', plain,
% 1.64/1.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.64/1.87         ((v5_relat_1 @ X8 @ X10)
% 1.64/1.87          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.64/1.87  thf('78', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 1.64/1.87      inference('sup-', [status(thm)], ['76', '77'])).
% 1.64/1.87  thf('79', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 1.64/1.87      inference('demod', [status(thm)], ['70', '75', '78'])).
% 1.64/1.87  thf(fc9_relat_1, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.64/1.87       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.64/1.87  thf('80', plain,
% 1.64/1.87      (![X6 : $i]:
% 1.64/1.87         (~ (v1_xboole_0 @ (k2_relat_1 @ X6))
% 1.64/1.87          | ~ (v1_relat_1 @ X6)
% 1.64/1.87          | (v1_xboole_0 @ X6))),
% 1.64/1.87      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.64/1.87  thf('81', plain,
% 1.64/1.87      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 1.64/1.87      inference('sup-', [status(thm)], ['79', '80'])).
% 1.64/1.87  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.87      inference('demod', [status(thm)], ['73', '74'])).
% 1.64/1.87  thf('83', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 1.64/1.87      inference('demod', [status(thm)], ['81', '82'])).
% 1.64/1.87  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.64/1.87  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.64/1.87  thf('86', plain, ((v1_xboole_0 @ sk_C)),
% 1.64/1.87      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.64/1.87  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.64/1.87  thf(t8_boole, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.64/1.87  thf('88', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [t8_boole])).
% 1.64/1.87  thf('89', plain,
% 1.64/1.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['87', '88'])).
% 1.64/1.87  thf('90', plain, (((k1_xboole_0) = (sk_C))),
% 1.64/1.87      inference('sup-', [status(thm)], ['86', '89'])).
% 1.64/1.87  thf('91', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.64/1.87      inference('demod', [status(thm)], ['35', '40', '43'])).
% 1.64/1.87  thf('92', plain,
% 1.64/1.87      (![X6 : $i]:
% 1.64/1.87         (~ (v1_xboole_0 @ (k2_relat_1 @ X6))
% 1.64/1.87          | ~ (v1_relat_1 @ X6)
% 1.64/1.87          | (v1_xboole_0 @ X6))),
% 1.64/1.87      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.64/1.87  thf('93', plain,
% 1.64/1.87      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | ~ (v1_relat_1 @ sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['91', '92'])).
% 1.64/1.87  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 1.64/1.87      inference('demod', [status(thm)], ['38', '39'])).
% 1.64/1.87  thf('95', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 1.64/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.64/1.87  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.64/1.87  thf('98', plain, ((v1_xboole_0 @ sk_B)),
% 1.64/1.87      inference('demod', [status(thm)], ['95', '96', '97'])).
% 1.64/1.87  thf('99', plain,
% 1.64/1.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['87', '88'])).
% 1.64/1.87  thf('100', plain, (((k1_xboole_0) = (sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['98', '99'])).
% 1.64/1.87  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.64/1.87  thf('101', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.87      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.64/1.87  thf(t67_funct_1, axiom,
% 1.64/1.87    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.64/1.87  thf('102', plain,
% 1.64/1.87      (![X7 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X7)) = (k6_relat_1 @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t67_funct_1])).
% 1.64/1.87  thf('103', plain,
% 1.64/1.87      (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['101', '102'])).
% 1.64/1.87  thf('104', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.87      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.64/1.87  thf('105', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['103', '104'])).
% 1.64/1.87  thf('106', plain,
% 1.64/1.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('107', plain,
% 1.64/1.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.64/1.87         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 1.64/1.87          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['57'])).
% 1.64/1.87  thf('108', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 1.64/1.87      inference('sup-', [status(thm)], ['106', '107'])).
% 1.64/1.87  thf('109', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf('110', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.87      inference('demod', [status(thm)], ['55', '59'])).
% 1.64/1.87  thf('111', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 1.64/1.87      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.64/1.87  thf('112', plain, (((k1_xboole_0) = (sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['98', '99'])).
% 1.64/1.87  thf('113', plain, (((k1_xboole_0) = (sk_B))),
% 1.64/1.87      inference('sup-', [status(thm)], ['98', '99'])).
% 1.64/1.87  thf('114', plain,
% 1.64/1.87      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.64/1.87      inference('demod', [status(thm)], ['111', '112', '113'])).
% 1.64/1.87  thf('115', plain, ($false),
% 1.64/1.87      inference('demod', [status(thm)], ['62', '90', '100', '105', '114'])).
% 1.64/1.87  
% 1.64/1.87  % SZS output end Refutation
% 1.64/1.87  
% 1.64/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
