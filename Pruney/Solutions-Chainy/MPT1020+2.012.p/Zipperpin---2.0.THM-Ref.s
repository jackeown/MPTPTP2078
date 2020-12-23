%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCeihvthHj

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:02 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  142 (1247 expanded)
%              Number of leaves         :   36 ( 380 expanded)
%              Depth                    :   17
%              Number of atoms          : 1142 (32469 expanded)
%              Number of equality atoms :   61 ( 464 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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

thf('10',plain,(
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

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34
        = ( k2_funct_1 @ X37 ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X35 @ X35 @ X36 @ X37 @ X34 ) @ ( k6_partfun1 @ X36 ) )
      | ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
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
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','39','45'])).

thf('47',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('74',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','66','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('91',plain,(
    v1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('93',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('100',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('102',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('103',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['94','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCeihvthHj
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 1424 iterations in 1.259s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.51/1.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.51/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.51/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.51/1.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.71  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.51/1.71  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.51/1.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.51/1.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.51/1.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.71  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.51/1.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.51/1.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.51/1.71  thf(t87_funct_2, conjecture,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( v3_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71       ( ![C:$i]:
% 1.51/1.71         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.51/1.71             ( v3_funct_2 @ C @ A @ A ) & 
% 1.51/1.71             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71           ( ( r2_relset_1 @
% 1.51/1.71               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.51/1.71               ( k6_partfun1 @ A ) ) =>
% 1.51/1.71             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 1.51/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.71    (~( ![A:$i,B:$i]:
% 1.51/1.71        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.51/1.71            ( v3_funct_2 @ B @ A @ A ) & 
% 1.51/1.71            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71          ( ![C:$i]:
% 1.51/1.71            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.51/1.71                ( v3_funct_2 @ C @ A @ A ) & 
% 1.51/1.71                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71              ( ( r2_relset_1 @
% 1.51/1.71                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.51/1.71                  ( k6_partfun1 @ A ) ) =>
% 1.51/1.71                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 1.51/1.71    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 1.51/1.71  thf('0', plain,
% 1.51/1.71      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('1', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_k2_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( v3_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.51/1.71  thf('2', plain,
% 1.51/1.71      (![X28 : $i, X29 : $i]:
% 1.51/1.71         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 1.51/1.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.51/1.71          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 1.51/1.71          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 1.51/1.71          | ~ (v1_funct_1 @ X28))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.51/1.71  thf('3', plain,
% 1.51/1.71      ((~ (v1_funct_1 @ sk_B)
% 1.51/1.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['1', '2'])).
% 1.51/1.71  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 1.51/1.71  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['0', '7'])).
% 1.51/1.71  thf('9', plain,
% 1.51/1.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.51/1.71        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 1.51/1.71        (k6_partfun1 @ sk_A))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('10', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(t36_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71       ( ![D:$i]:
% 1.51/1.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.51/1.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.51/1.71           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.51/1.71               ( r2_relset_1 @
% 1.51/1.71                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.51/1.71                 ( k6_partfun1 @ A ) ) & 
% 1.51/1.71               ( v2_funct_1 @ C ) ) =>
% 1.51/1.71             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.51/1.71  thf('11', plain,
% 1.51/1.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.71         (~ (v1_funct_1 @ X34)
% 1.51/1.71          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 1.51/1.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.51/1.71          | ((X34) = (k2_funct_1 @ X37))
% 1.51/1.71          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 1.51/1.71               (k1_partfun1 @ X36 @ X35 @ X35 @ X36 @ X37 @ X34) @ 
% 1.51/1.71               (k6_partfun1 @ X36))
% 1.51/1.71          | ((X35) = (k1_xboole_0))
% 1.51/1.71          | ((X36) = (k1_xboole_0))
% 1.51/1.71          | ~ (v2_funct_1 @ X37)
% 1.51/1.71          | ((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 1.51/1.71          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.51/1.71          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 1.51/1.71          | ~ (v1_funct_1 @ X37))),
% 1.51/1.71      inference('cnf', [status(esa)], [t36_funct_2])).
% 1.51/1.71  thf('12', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.51/1.71          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ((sk_A) = (k1_xboole_0))
% 1.51/1.71          | ((sk_A) = (k1_xboole_0))
% 1.51/1.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.51/1.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.51/1.71               (k6_partfun1 @ sk_A))
% 1.51/1.71          | ((sk_C) = (k2_funct_1 @ X0))
% 1.51/1.71          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.51/1.71          | ~ (v1_funct_1 @ sk_C))),
% 1.51/1.71      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.71  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('15', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.51/1.71          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ((sk_A) = (k1_xboole_0))
% 1.51/1.71          | ((sk_A) = (k1_xboole_0))
% 1.51/1.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.51/1.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.51/1.71               (k6_partfun1 @ sk_A))
% 1.51/1.71          | ((sk_C) = (k2_funct_1 @ X0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.51/1.71  thf('16', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (((sk_C) = (k2_funct_1 @ X0))
% 1.51/1.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.51/1.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.51/1.71               (k6_partfun1 @ sk_A))
% 1.51/1.71          | ((sk_A) = (k1_xboole_0))
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.51/1.71          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.51/1.71          | ~ (v1_funct_1 @ X0))),
% 1.51/1.71      inference('simplify', [status(thm)], ['15'])).
% 1.51/1.71  thf('17', plain,
% 1.51/1.71      ((~ (v1_funct_1 @ sk_B)
% 1.51/1.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.51/1.71        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 1.51/1.71        | ~ (v2_funct_1 @ sk_B)
% 1.51/1.71        | ((sk_A) = (k1_xboole_0))
% 1.51/1.71        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['9', '16'])).
% 1.51/1.71  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('20', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('21', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_k2_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.51/1.71  thf('22', plain,
% 1.51/1.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.51/1.71         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.51/1.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.71  thf('23', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['21', '22'])).
% 1.51/1.71  thf('24', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc2_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.51/1.71         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.51/1.71  thf('25', plain,
% 1.51/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.51/1.71         (~ (v1_funct_1 @ X21)
% 1.51/1.71          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 1.51/1.71          | (v2_funct_2 @ X21 @ X23)
% 1.51/1.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.51/1.71  thf('26', plain,
% 1.51/1.71      (((v2_funct_2 @ sk_B @ sk_A)
% 1.51/1.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ~ (v1_funct_1 @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['24', '25'])).
% 1.51/1.71  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.51/1.71      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.51/1.71  thf(d3_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.51/1.71       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.51/1.71  thf('30', plain,
% 1.51/1.71      (![X24 : $i, X25 : $i]:
% 1.51/1.71         (~ (v2_funct_2 @ X25 @ X24)
% 1.51/1.71          | ((k2_relat_1 @ X25) = (X24))
% 1.51/1.71          | ~ (v5_relat_1 @ X25 @ X24)
% 1.51/1.71          | ~ (v1_relat_1 @ X25))),
% 1.51/1.71      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.51/1.71  thf('31', plain,
% 1.51/1.71      ((~ (v1_relat_1 @ sk_B)
% 1.51/1.71        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.51/1.71        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['29', '30'])).
% 1.51/1.71  thf('32', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc1_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( v1_relat_1 @ C ) ))).
% 1.51/1.71  thf('33', plain,
% 1.51/1.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.51/1.71         ((v1_relat_1 @ X2)
% 1.51/1.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.71  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.71      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.71  thf('35', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc2_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.51/1.71  thf('36', plain,
% 1.51/1.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.51/1.71         ((v5_relat_1 @ X5 @ X7)
% 1.51/1.71          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.51/1.71  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.51/1.71      inference('sup-', [status(thm)], ['35', '36'])).
% 1.51/1.71  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.51/1.71      inference('demod', [status(thm)], ['31', '34', '37'])).
% 1.51/1.71  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 1.51/1.71      inference('demod', [status(thm)], ['23', '38'])).
% 1.51/1.71  thf('40', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('41', plain,
% 1.51/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.51/1.71         (~ (v1_funct_1 @ X21)
% 1.51/1.71          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 1.51/1.71          | (v2_funct_1 @ X21)
% 1.51/1.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.51/1.71  thf('42', plain,
% 1.51/1.71      (((v2_funct_1 @ sk_B)
% 1.51/1.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ~ (v1_funct_1 @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['40', '41'])).
% 1.51/1.71  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 1.51/1.71      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.51/1.71  thf('46', plain,
% 1.51/1.71      ((((sk_A) != (sk_A))
% 1.51/1.71        | ((sk_A) = (k1_xboole_0))
% 1.51/1.71        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 1.51/1.71      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 1.51/1.71  thf('47', plain,
% 1.51/1.71      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['46'])).
% 1.51/1.71  thf('48', plain,
% 1.51/1.71      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['0', '7'])).
% 1.51/1.71  thf('49', plain,
% 1.51/1.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['47', '48'])).
% 1.51/1.71  thf('50', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_r2_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.51/1.71  thf('51', plain,
% 1.51/1.71      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.71         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.51/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.51/1.71          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 1.51/1.71          | ((X17) != (X20)))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.51/1.71  thf('52', plain,
% 1.51/1.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.71         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.51/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.51/1.71      inference('simplify', [status(thm)], ['51'])).
% 1.51/1.71  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.51/1.71      inference('sup-', [status(thm)], ['50', '52'])).
% 1.51/1.71  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('56', plain,
% 1.51/1.71      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['8', '54', '55'])).
% 1.51/1.71  thf('57', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc3_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( v1_xboole_0 @ A ) =>
% 1.51/1.71       ( ![C:$i]:
% 1.51/1.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71           ( v1_xboole_0 @ C ) ) ) ))).
% 1.51/1.71  thf('58', plain,
% 1.51/1.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.71         (~ (v1_xboole_0 @ X8)
% 1.51/1.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 1.51/1.71          | (v1_xboole_0 @ X9))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.51/1.71  thf('59', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.51/1.71      inference('sup-', [status(thm)], ['57', '58'])).
% 1.51/1.71  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.51/1.71  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.71  thf('62', plain, ((v1_xboole_0 @ sk_C)),
% 1.51/1.71      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.51/1.71  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.71  thf(t8_boole, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.51/1.71  thf('64', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t8_boole])).
% 1.51/1.71  thf('65', plain,
% 1.51/1.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.71  thf('66', plain, (((k1_xboole_0) = (sk_C))),
% 1.51/1.71      inference('sup-', [status(thm)], ['62', '65'])).
% 1.51/1.71  thf('67', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('68', plain,
% 1.51/1.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.71         (~ (v1_xboole_0 @ X8)
% 1.51/1.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 1.51/1.71          | (v1_xboole_0 @ X9))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.51/1.71  thf('69', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 1.51/1.71      inference('sup-', [status(thm)], ['67', '68'])).
% 1.51/1.71  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.71  thf('72', plain, ((v1_xboole_0 @ sk_B)),
% 1.51/1.71      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.51/1.71  thf('73', plain,
% 1.51/1.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.71  thf('74', plain, (((k1_xboole_0) = (sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.71  thf('75', plain,
% 1.51/1.71      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 1.51/1.71          (k2_funct_1 @ k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['56', '66', '74'])).
% 1.51/1.71  thf('76', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(dt_k2_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( v3_funct_2 @ B @ A @ A ) & 
% 1.51/1.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.51/1.71       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.51/1.71         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.51/1.71         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.51/1.71         ( m1_subset_1 @
% 1.51/1.71           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.51/1.71  thf('77', plain,
% 1.51/1.71      (![X26 : $i, X27 : $i]:
% 1.51/1.71         ((m1_subset_1 @ (k2_funct_2 @ X26 @ X27) @ 
% 1.51/1.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 1.51/1.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 1.51/1.71          | ~ (v3_funct_2 @ X27 @ X26 @ X26)
% 1.51/1.71          | ~ (v1_funct_2 @ X27 @ X26 @ X26)
% 1.51/1.71          | ~ (v1_funct_1 @ X27))),
% 1.51/1.71      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.51/1.71  thf('78', plain,
% 1.51/1.71      ((~ (v1_funct_1 @ sk_B)
% 1.51/1.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.51/1.71        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.51/1.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.51/1.71      inference('sup-', [status(thm)], ['76', '77'])).
% 1.51/1.71  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('80', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('81', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('82', plain,
% 1.51/1.71      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.51/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 1.51/1.71  thf('83', plain,
% 1.51/1.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.71         (~ (v1_xboole_0 @ X8)
% 1.51/1.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 1.51/1.71          | (v1_xboole_0 @ X9))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.51/1.71  thf('84', plain,
% 1.51/1.71      (((v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 1.51/1.71      inference('sup-', [status(thm)], ['82', '83'])).
% 1.51/1.71  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 1.51/1.71  thf('86', plain,
% 1.51/1.71      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 1.51/1.71      inference('demod', [status(thm)], ['84', '85'])).
% 1.51/1.71  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.71  thf('89', plain, ((v1_xboole_0 @ (k2_funct_1 @ sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.51/1.71  thf('90', plain, (((k1_xboole_0) = (sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.71  thf('91', plain, ((v1_xboole_0 @ (k2_funct_1 @ k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['89', '90'])).
% 1.51/1.71  thf('92', plain,
% 1.51/1.71      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.71  thf('93', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['91', '92'])).
% 1.51/1.71  thf('94', plain,
% 1.51/1.71      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('demod', [status(thm)], ['75', '93'])).
% 1.51/1.71  thf('95', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('96', plain,
% 1.51/1.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.71         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.51/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.51/1.71      inference('simplify', [status(thm)], ['51'])).
% 1.51/1.71  thf('97', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 1.51/1.71      inference('sup-', [status(thm)], ['95', '96'])).
% 1.51/1.71  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['49', '53'])).
% 1.51/1.71  thf('100', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 1.51/1.71      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.51/1.71  thf('101', plain, (((k1_xboole_0) = (sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.71  thf('102', plain, (((k1_xboole_0) = (sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.71  thf('103', plain,
% 1.51/1.71      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.51/1.71      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.51/1.71  thf('104', plain, ($false), inference('demod', [status(thm)], ['94', '103'])).
% 1.51/1.71  
% 1.51/1.71  % SZS output end Refutation
% 1.51/1.71  
% 1.51/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
