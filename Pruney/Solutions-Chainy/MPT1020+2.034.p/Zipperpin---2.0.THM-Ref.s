%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rvpaqQKjc1

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 647 expanded)
%              Number of leaves         :   44 ( 212 expanded)
%              Depth                    :   14
%              Number of atoms          : 1394 (14790 expanded)
%              Number of equality atoms :  116 ( 288 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( X37
        = ( k2_funct_1 @ X40 ) )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X38 @ X38 @ X39 @ X40 @ X37 ) @ ( k6_partfun1 @ X39 ) )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_2 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_2 @ X27 @ X26 )
      | ( ( k2_relat_1 @ X27 )
        = X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_2 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('59',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_2 @ X27 @ X26 )
      | ( ( k2_relat_1 @ X27 )
        = X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['64','67','70'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('87',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('88',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('90',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('93',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('94',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_partfun1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('97',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','99'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('102',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('106',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('107',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('108',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('110',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('111',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('112',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('114',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('118',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','109','112','113','116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','120'])).

thf('122',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('123',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('125',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('126',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('128',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['56','78','86','123','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rvpaqQKjc1
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 148 iterations in 0.072s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.53  thf(t87_funct_2, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.22/0.53             ( v3_funct_2 @ C @ A @ A ) & 
% 0.22/0.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53           ( ( r2_relset_1 @
% 0.22/0.53               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.22/0.53               ( k6_partfun1 @ A ) ) =>
% 0.22/0.53             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.53            ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53          ( ![C:$i]:
% 0.22/0.53            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.22/0.53                ( v3_funct_2 @ C @ A @ A ) & 
% 0.22/0.53                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53              ( ( r2_relset_1 @
% 0.22/0.53                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.22/0.53                  ( k6_partfun1 @ A ) ) =>
% 0.22/0.53                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k2_funct_2, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X30 : $i, X31 : $i]:
% 0.22/0.53         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.22/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.22/0.53          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.22/0.53          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.22/0.53          | ~ (v1_funct_1 @ X30))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.53        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.22/0.53  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.53        (k6_partfun1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t36_funct_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ![D:$i]:
% 0.22/0.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.22/0.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.22/0.53           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.22/0.53               ( r2_relset_1 @
% 0.22/0.53                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.22/0.53                 ( k6_partfun1 @ A ) ) & 
% 0.22/0.53               ( v2_funct_1 @ C ) ) =>
% 0.22/0.53             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.53               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.53         (~ (v1_funct_1 @ X37)
% 0.22/0.53          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.22/0.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.22/0.53          | ((X37) = (k2_funct_1 @ X40))
% 0.22/0.53          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 0.22/0.53               (k1_partfun1 @ X39 @ X38 @ X38 @ X39 @ X40 @ X37) @ 
% 0.22/0.53               (k6_partfun1 @ X39))
% 0.22/0.53          | ((X38) = (k1_xboole_0))
% 0.22/0.53          | ((X39) = (k1_xboole_0))
% 0.22/0.53          | ~ (v2_funct_1 @ X40)
% 0.22/0.53          | ((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.22/0.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.22/0.53          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.22/0.53          | ~ (v1_funct_1 @ X40))),
% 0.22/0.53      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.53               (k6_partfun1 @ sk_A))
% 0.22/0.53          | ((sk_C) = (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.53               (k6_partfun1 @ sk_A))
% 0.22/0.53          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((sk_C) = (k2_funct_1 @ X0))
% 0.22/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.53               (k6_partfun1 @ sk_A))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (v2_funct_1 @ X0)
% 0.22/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.53          | ~ (v1_funct_1 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.53        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.53        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.22/0.53        | ~ (v2_funct_1 @ sk_B)
% 0.22/0.53        | ((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.53  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.53         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.22/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_funct_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.53         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.53         (~ (v1_funct_1 @ X23)
% 0.22/0.53          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.22/0.53          | (v2_funct_2 @ X23 @ X25)
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (((v2_funct_2 @ sk_B @ sk_A)
% 0.22/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.53        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.53  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.53  thf(d3_funct_2, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i]:
% 0.22/0.54         (~ (v2_funct_2 @ X27 @ X26)
% 0.22/0.54          | ((k2_relat_1 @ X27) = (X26))
% 0.22/0.54          | ~ (v5_relat_1 @ X27 @ X26)
% 0.22/0.54          | ~ (v1_relat_1 @ X27))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.54        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.22/0.54        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X10)
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         ((v5_relat_1 @ X13 @ X15)
% 0.22/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.22/0.54  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (~ (v1_funct_1 @ X23)
% 0.22/0.54          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.22/0.54          | (v2_funct_1 @ X23)
% 0.22/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (((v2_funct_1 @ sk_B)
% 0.22/0.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      ((((sk_A) != (sk_A))
% 0.22/0.54        | ((sk_A) = (k1_xboole_0))
% 0.22/0.54        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_r2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.54          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 0.22/0.54          | ((X19) != (X22)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.22/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.54  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '52'])).
% 0.22/0.54  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['49', '53'])).
% 0.22/0.54  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['49', '53'])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '54', '55'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (~ (v1_funct_1 @ X23)
% 0.22/0.54          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.22/0.54          | (v2_funct_2 @ X23 @ X25)
% 0.22/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (((v2_funct_2 @ sk_C @ sk_A)
% 0.22/0.54        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.54  thf('60', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('62', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i]:
% 0.22/0.54         (~ (v2_funct_2 @ X27 @ X26)
% 0.22/0.54          | ((k2_relat_1 @ X27) = (X26))
% 0.22/0.54          | ~ (v5_relat_1 @ X27 @ X26)
% 0.22/0.54          | ~ (v1_relat_1 @ X27))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.54        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.22/0.54        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X10)
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         ((v5_relat_1 @ X13 @ X15)
% 0.22/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('70', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.54  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['64', '67', '70'])).
% 0.22/0.54  thf(t64_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.22/0.54          | ((X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      ((((sk_A) != (k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.54  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.54  thf('75', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.54  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['49', '53'])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.54  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.54  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.22/0.54  thf('80', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.22/0.54          | ((X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      ((((sk_A) != (k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.54  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('83', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.54  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['49', '53'])).
% 0.22/0.54  thf('85', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.22/0.54  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['85'])).
% 0.22/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.54  thf('87', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.54  thf('88', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('89', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.54  thf(t71_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.54  thf('90', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf('91', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('92', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 0.22/0.54      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.54  thf(t80_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.22/0.54  thf('93', plain,
% 0.22/0.54      (![X3 : $i]:
% 0.22/0.54         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 0.22/0.54          | ~ (v1_relat_1 @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.22/0.54  thf('94', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('95', plain,
% 0.22/0.54      (![X3 : $i]:
% 0.22/0.54         (((k5_relat_1 @ X3 @ (k6_partfun1 @ (k2_relat_1 @ X3))) = (X3))
% 0.22/0.54          | ~ (v1_relat_1 @ X3))),
% 0.22/0.54      inference('demod', [status(thm)], ['93', '94'])).
% 0.22/0.54  thf('96', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.22/0.54            = (k6_partfun1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['92', '95'])).
% 0.22/0.54  thf(fc3_funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.54  thf('97', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.54  thf('98', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('99', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.22/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.22/0.54  thf('100', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.22/0.54           = (k6_partfun1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['96', '99'])).
% 0.22/0.54  thf(t64_funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.54           ( ( ( v2_funct_1 @ A ) & 
% 0.22/0.54               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.22/0.54               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.22/0.54             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('101', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X8)
% 0.22/0.54          | ~ (v1_funct_1 @ X8)
% 0.22/0.54          | ((X8) = (k2_funct_1 @ X9))
% 0.22/0.54          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.22/0.54          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.22/0.54          | ~ (v2_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.22/0.54  thf('102', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('103', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X8)
% 0.22/0.54          | ~ (v1_funct_1 @ X8)
% 0.22/0.54          | ((X8) = (k2_funct_1 @ X9))
% 0.22/0.54          | ((k5_relat_1 @ X8 @ X9) != (k6_partfun1 @ (k2_relat_1 @ X9)))
% 0.22/0.54          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.22/0.54          | ~ (v2_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('demod', [status(thm)], ['101', '102'])).
% 0.22/0.54  thf('104', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k6_partfun1 @ X0)
% 0.22/0.54            != (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0))))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.54          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.54          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.54          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.54              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 0.22/0.54          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.22/0.54          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['100', '103'])).
% 0.22/0.54  thf('105', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 0.22/0.54      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.54  thf('106', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.22/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.22/0.54  thf('107', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.54  thf('108', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('109', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 0.22/0.54      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.54  thf(fc4_funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.54  thf('110', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.54  thf('111', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('112', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.22/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.22/0.54  thf('113', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 0.22/0.54      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.54  thf('114', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf('115', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('116', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['114', '115'])).
% 0.22/0.54  thf('117', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 0.22/0.54      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.54  thf('118', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.22/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.22/0.54  thf('119', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.22/0.54          | ((X0) != (X0))
% 0.22/0.54          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 0.22/0.54      inference('demod', [status(thm)],
% 0.22/0.54                ['104', '105', '106', '109', '112', '113', '116', '117', '118'])).
% 0.22/0.54  thf('120', plain,
% 0.22/0.54      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['119'])).
% 0.22/0.54  thf('121', plain,
% 0.22/0.54      (((k6_partfun1 @ k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['89', '120'])).
% 0.22/0.54  thf('122', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.54  thf('123', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['121', '122'])).
% 0.22/0.54  thf('124', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.54  thf(dt_k6_partfun1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( m1_subset_1 @
% 0.22/0.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.22/0.54  thf('125', plain,
% 0.22/0.54      (![X29 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.22/0.54  thf('126', plain,
% 0.22/0.54      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.22/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['124', '125'])).
% 0.22/0.54  thf('127', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.22/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.54  thf('128', plain,
% 0.22/0.54      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['126', '127'])).
% 0.22/0.54  thf('129', plain, ($false),
% 0.22/0.54      inference('demod', [status(thm)], ['56', '78', '86', '123', '128'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
