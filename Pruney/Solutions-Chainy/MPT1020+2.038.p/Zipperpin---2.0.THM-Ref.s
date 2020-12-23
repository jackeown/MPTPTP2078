%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hCvY3I9E2t

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 814 expanded)
%              Number of leaves         :   42 ( 259 expanded)
%              Depth                    :   16
%              Number of atoms          : 1431 (19160 expanded)
%              Number of equality atoms :  117 ( 395 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( X35
        = ( k2_funct_1 @ X38 ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X36 @ X36 @ X37 @ X38 @ X35 ) @ ( k6_partfun1 @ X37 ) )
      | ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( X35
        = ( k2_funct_1 @ X38 ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X36 @ X36 @ X37 @ X38 @ X35 ) @ ( k6_relat_1 @ X37 ) )
      | ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('91',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('98',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

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

thf('102',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X7 @ X6 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('105',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('106',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('109',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
       != ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_relat_1 @ X0 )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k6_relat_1 @ k1_xboole_0 )
      = ( k2_funct_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['96','111'])).

thf('113',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf('114',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('118',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('121',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('122',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('123',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('126',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['60','82','90','119','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hCvY3I9E2t
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 148 iterations in 0.051s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(t87_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.50             ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.50             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50           ( ( r2_relset_1 @
% 0.21/0.50               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.50               ( k6_partfun1 @ A ) ) =>
% 0.21/0.50             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50            ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.50                ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.50                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50              ( ( r2_relset_1 @
% 0.21/0.50                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.50                  ( k6_partfun1 @ A ) ) =>
% 0.21/0.50                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.21/0.50          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.21/0.50          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.21/0.50          | ~ (v1_funct_1 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.50  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50        (k6_partfun1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('10', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50        (k6_relat_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t36_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.50           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.50               ( r2_relset_1 @
% 0.21/0.50                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.21/0.50                 ( k6_partfun1 @ A ) ) & 
% 0.21/0.50               ( v2_funct_1 @ C ) ) =>
% 0.21/0.50             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X35)
% 0.21/0.50          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.21/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.21/0.50          | ((X35) = (k2_funct_1 @ X38))
% 0.21/0.50          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 0.21/0.50               (k1_partfun1 @ X37 @ X36 @ X36 @ X37 @ X38 @ X35) @ 
% 0.21/0.50               (k6_partfun1 @ X37))
% 0.21/0.50          | ((X36) = (k1_xboole_0))
% 0.21/0.50          | ((X37) = (k1_xboole_0))
% 0.21/0.50          | ~ (v2_funct_1 @ X38)
% 0.21/0.50          | ((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.21/0.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.21/0.50          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.21/0.50          | ~ (v1_funct_1 @ X38))),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.21/0.50  thf('14', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X35)
% 0.21/0.50          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.21/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.21/0.50          | ((X35) = (k2_funct_1 @ X38))
% 0.21/0.50          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 0.21/0.50               (k1_partfun1 @ X37 @ X36 @ X36 @ X37 @ X38 @ X35) @ 
% 0.21/0.50               (k6_relat_1 @ X37))
% 0.21/0.50          | ((X36) = (k1_xboole_0))
% 0.21/0.50          | ((X37) = (k1_xboole_0))
% 0.21/0.50          | ~ (v2_funct_1 @ X38)
% 0.21/0.50          | ((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.21/0.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.21/0.50          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.21/0.50          | ~ (v1_funct_1 @ X38))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.50               (k6_relat_1 @ sk_A))
% 0.21/0.50          | ((sk_C) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.50  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.50               (k6_relat_1 @ sk_A))
% 0.21/0.50          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_C) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.50               (k6_relat_1 @ sk_A))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.21/0.50        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '20'])).
% 0.21/0.50  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.50         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X21)
% 0.21/0.50          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.50          | (v2_funct_2 @ X21 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((v2_funct_2 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.50  thf(d3_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (v2_funct_2 @ X25 @ X24)
% 0.21/0.50          | ((k2_relat_1 @ X25) = (X24))
% 0.21/0.50          | ~ (v5_relat_1 @ X25 @ X24)
% 0.21/0.50          | ~ (v1_relat_1 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.21/0.50        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('41', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.21/0.50  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X21)
% 0.21/0.50          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.50          | (v2_funct_1 @ X21)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((sk_A) != (sk_A))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '22', '23', '24', '43', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.50          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.21/0.50          | ((X17) != (X20)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.50  thf('57', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '56'])).
% 0.21/0.50  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '57'])).
% 0.21/0.50  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '57'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X21)
% 0.21/0.50          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.50          | (v2_funct_2 @ X21 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((v2_funct_2 @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (v2_funct_2 @ X25 @ X24)
% 0.21/0.50          | ((k2_relat_1 @ X25) = (X24))
% 0.21/0.50          | ~ (v5_relat_1 @ X25 @ X24)
% 0.21/0.50          | ~ (v1_relat_1 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.21/0.50        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['68', '71', '74'])).
% 0.21/0.50  thf(t64_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      ((((sk_A) != (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.50  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('79', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.50  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '57'])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.50  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.50  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      ((((sk_A) != (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.50  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('87', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.50  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '57'])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.50  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['89'])).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('91', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.50  thf(fc4_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('94', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.50  thf('96', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.50  thf('97', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(t80_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      (![X3 : $i]:
% 0.21/0.50         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 0.21/0.50          | ~ (v1_relat_1 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.21/0.50            = (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['97', '98'])).
% 0.21/0.50  thf('100', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.21/0.50           = (k6_relat_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.50  thf(t63_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.50               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.50               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X6)
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ((X6) = (k2_funct_1 @ X7))
% 0.21/0.50          | ((k5_relat_1 @ X7 @ X6) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.21/0.50          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.21/0.50          | ~ (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.21/0.50  thf('103', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50              != (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ((k6_relat_1 @ X0) = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.50  thf('104', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('105', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('106', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('107', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('108', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('109', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('110', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ X0) != (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((X0) != (X0))
% 0.21/0.50          | ((k6_relat_1 @ X0) = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['103', '104', '105', '106', '107', '108', '109'])).
% 0.21/0.50  thf('111', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ X0) = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['110'])).
% 0.21/0.50  thf('112', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50        | ((k6_relat_1 @ k1_xboole_0)
% 0.21/0.50            = (k2_funct_1 @ (k6_relat_1 @ k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['96', '111'])).
% 0.21/0.50  thf('113', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.50  thf('114', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.50  thf('115', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.21/0.50  thf('116', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('117', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['89'])).
% 0.21/0.50  thf('118', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['116', '117'])).
% 0.21/0.50  thf('119', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['115', '118'])).
% 0.21/0.50  thf('120', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.50  thf(dt_k6_partfun1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( m1_subset_1 @
% 0.21/0.50         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.50       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.21/0.50  thf('121', plain,
% 0.21/0.50      (![X27 : $i]:
% 0.21/0.50         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.21/0.50  thf('122', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('123', plain,
% 0.21/0.50      (![X27 : $i]:
% 0.21/0.50         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.21/0.50      inference('demod', [status(thm)], ['121', '122'])).
% 0.21/0.50  thf('124', plain,
% 0.21/0.50      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['120', '123'])).
% 0.21/0.50  thf('125', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.50  thf('126', plain,
% 0.21/0.50      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['124', '125'])).
% 0.21/0.50  thf('127', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['60', '82', '90', '119', '126'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
