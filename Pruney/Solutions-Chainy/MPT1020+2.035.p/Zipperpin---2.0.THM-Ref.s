%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.50ZHhOGafD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 857 expanded)
%              Number of leaves         :   45 ( 276 expanded)
%              Depth                    :   16
%              Number of atoms          : 1494 (19019 expanded)
%              Number of equality atoms :  132 ( 412 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['89','92'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('95',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

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

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_partfun1 @ X1 ) ) )
      | ( ( k6_partfun1 @ X1 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('104',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('105',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != X1 )
      | ( ( k6_partfun1 @ X1 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['100','103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k6_partfun1 @ ( k1_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ k1_xboole_0 ) )
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['93','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['89','92'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('111',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('112',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('114',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('115',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('118',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('119',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('121',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['113','114'])).

thf('122',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('123',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('124',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['89','92'])).

thf('128',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('129',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['89','92'])).

thf('130',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('131',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','116','119','120','121','126','127','128','129','130'])).

thf('132',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf('135',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','135'])).

thf('137',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('138',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('139',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('141',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['56','78','86','136','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.50ZHhOGafD
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 150 iterations in 0.073s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.37/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.55  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(t87_funct_2, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.55         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.55             ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.55             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55           ( ( r2_relset_1 @
% 0.37/0.55               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.37/0.55               ( k6_partfun1 @ A ) ) =>
% 0.37/0.55             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.55            ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.55            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55          ( ![C:$i]:
% 0.37/0.55            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.55                ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.55                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55              ( ( r2_relset_1 @
% 0.37/0.55                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.37/0.55                  ( k6_partfun1 @ A ) ) =>
% 0.37/0.55                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k2_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.55         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X30 : $i, X31 : $i]:
% 0.37/0.55         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.37/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.37/0.55          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.37/0.55          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.37/0.55          | ~ (v1_funct_1 @ X30))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      ((~ (v1_funct_1 @ sk_B)
% 0.37/0.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.55        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.37/0.55  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.55        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.37/0.55        (k6_partfun1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t36_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.37/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.37/0.55           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.37/0.55               ( r2_relset_1 @
% 0.37/0.55                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.37/0.55                 ( k6_partfun1 @ A ) ) & 
% 0.37/0.55               ( v2_funct_1 @ C ) ) =>
% 0.37/0.55             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X37)
% 0.37/0.55          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.37/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.37/0.55          | ((X37) = (k2_funct_1 @ X40))
% 0.37/0.55          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 0.37/0.55               (k1_partfun1 @ X39 @ X38 @ X38 @ X39 @ X40 @ X37) @ 
% 0.37/0.55               (k6_partfun1 @ X39))
% 0.37/0.55          | ((X38) = (k1_xboole_0))
% 0.37/0.55          | ((X39) = (k1_xboole_0))
% 0.37/0.55          | ~ (v2_funct_1 @ X40)
% 0.37/0.55          | ((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.37/0.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.37/0.55          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.37/0.55          | ~ (v1_funct_1 @ X40))),
% 0.37/0.55      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.55               (k6_partfun1 @ sk_A))
% 0.37/0.55          | ((sk_C) = (k2_funct_1 @ X0))
% 0.37/0.55          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.55               (k6_partfun1 @ sk_A))
% 0.37/0.55          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((sk_C) = (k2_funct_1 @ X0))
% 0.37/0.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.37/0.55               (k6_partfun1 @ sk_A))
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.37/0.55          | ~ (v1_funct_1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((~ (v1_funct_1 @ sk_B)
% 0.37/0.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.55        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.55        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.37/0.55        | ~ (v2_funct_1 @ sk_B)
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.37/0.55  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.55         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.55         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X23)
% 0.37/0.55          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.37/0.55          | (v2_funct_2 @ X23 @ X25)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((v2_funct_2 @ sk_B @ sk_A)
% 0.37/0.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.37/0.55  thf(d3_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.37/0.55       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i]:
% 0.37/0.55         (~ (v2_funct_2 @ X27 @ X26)
% 0.37/0.55          | ((k2_relat_1 @ X27) = (X26))
% 0.37/0.55          | ~ (v5_relat_1 @ X27 @ X26)
% 0.37/0.55          | ~ (v1_relat_1 @ X27))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_B)
% 0.37/0.55        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.37/0.55        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( v1_relat_1 @ C ) ))).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         ((v1_relat_1 @ X10)
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.55  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.55         ((v5_relat_1 @ X13 @ X15)
% 0.37/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.37/0.55  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X23)
% 0.37/0.55          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.37/0.55          | (v2_funct_1 @ X23)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (((v2_funct_1 @ sk_B)
% 0.37/0.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      ((((sk_A) != (sk_A))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.37/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.37/0.55          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 0.37/0.55          | ((X19) != (X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.37/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.37/0.55  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '52'])).
% 0.37/0.55  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '53'])).
% 0.37/0.55  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '53'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['8', '54', '55'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X23)
% 0.37/0.55          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.37/0.55          | (v2_funct_2 @ X23 @ X25)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (((v2_funct_2 @ sk_C @ sk_A)
% 0.37/0.55        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf('60', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('62', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i]:
% 0.37/0.55         (~ (v2_funct_2 @ X27 @ X26)
% 0.37/0.55          | ((k2_relat_1 @ X27) = (X26))
% 0.37/0.55          | ~ (v5_relat_1 @ X27 @ X26)
% 0.37/0.55          | ~ (v1_relat_1 @ X27))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.37/0.55        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         ((v1_relat_1 @ X10)
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.55  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.55         ((v5_relat_1 @ X13 @ X15)
% 0.37/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('70', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.55  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['64', '67', '70'])).
% 0.37/0.55  thf(t64_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.55         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (![X3 : $i]:
% 0.37/0.55         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.37/0.55          | ((X3) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      ((((sk_A) != (k1_xboole_0))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.55  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('75', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['73', '74'])).
% 0.37/0.55  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '53'])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.37/0.55  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.37/0.55  thf('80', plain,
% 0.37/0.55      (![X3 : $i]:
% 0.37/0.55         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.37/0.55          | ((X3) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      ((((sk_A) != (k1_xboole_0))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.37/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('83', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.37/0.55  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '53'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.55  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['85'])).
% 0.37/0.55  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.55  thf('87', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.37/0.55  thf(redefinition_k6_partfun1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.37/0.55  thf('88', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('89', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf(t71_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.55  thf('90', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.55  thf('91', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('92', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.37/0.55      inference('demod', [status(thm)], ['90', '91'])).
% 0.37/0.55  thf('93', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['89', '92'])).
% 0.37/0.55  thf(t123_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.37/0.55  thf('94', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.37/0.55  thf('95', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.37/0.55  thf(t63_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55           ( ( ( v2_funct_1 @ A ) & 
% 0.37/0.55               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.37/0.55               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.37/0.55             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('97', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X8)
% 0.37/0.55          | ~ (v1_funct_1 @ X8)
% 0.37/0.55          | ((X8) = (k2_funct_1 @ X9))
% 0.37/0.55          | ((k5_relat_1 @ X9 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.37/0.55          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.37/0.55          | ~ (v2_funct_1 @ X9)
% 0.37/0.55          | ~ (v1_funct_1 @ X9)
% 0.37/0.55          | ~ (v1_relat_1 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.37/0.55  thf('98', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('99', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X8)
% 0.37/0.55          | ~ (v1_funct_1 @ X8)
% 0.37/0.55          | ((X8) = (k2_funct_1 @ X9))
% 0.37/0.55          | ((k5_relat_1 @ X9 @ X8) != (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.37/0.55          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.37/0.55          | ~ (v2_funct_1 @ X9)
% 0.37/0.55          | ~ (v1_funct_1 @ X9)
% 0.37/0.55          | ~ (v1_relat_1 @ X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['97', '98'])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k8_relat_1 @ X1 @ X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k6_partfun1 @ X1)))
% 0.37/0.55          | ((k6_partfun1 @ X1) = (k2_funct_1 @ X0))
% 0.37/0.55          | ~ (v1_funct_1 @ (k6_partfun1 @ X1))
% 0.37/0.55          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['96', '99'])).
% 0.37/0.55  thf('101', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.55  thf('102', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('103', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.37/0.55      inference('demod', [status(thm)], ['101', '102'])).
% 0.37/0.55  thf(fc4_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.55  thf('104', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.37/0.55  thf('105', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('106', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.37/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((k8_relat_1 @ X1 @ X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ((k2_relat_1 @ X0) != (X1))
% 0.37/0.55          | ((k6_partfun1 @ X1) = (k2_funct_1 @ X0))
% 0.37/0.55          | ~ (v1_funct_1 @ (k6_partfun1 @ X1)))),
% 0.37/0.55      inference('demod', [status(thm)], ['100', '103', '106'])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.37/0.55          | ((k6_partfun1 @ (k2_relat_1 @ X0)) = (k2_funct_1 @ X0))
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0)
% 0.37/0.55              != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['107'])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      ((((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.55          != (k6_partfun1 @ (k1_relat_1 @ k1_xboole_0)))
% 0.37/0.55        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.55        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.55        | ~ (v2_funct_1 @ k1_xboole_0)
% 0.37/0.55        | ((k6_partfun1 @ (k2_relat_1 @ k1_xboole_0))
% 0.37/0.55            = (k2_funct_1 @ k1_xboole_0))
% 0.37/0.55        | ~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['93', '108'])).
% 0.37/0.55  thf('110', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['89', '92'])).
% 0.37/0.55  thf(t126_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.37/0.55  thf('111', plain,
% 0.37/0.55      (![X2 : $i]:
% 0.37/0.55         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      ((((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.55        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['110', '111'])).
% 0.37/0.55  thf('113', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('114', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.37/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.55  thf('115', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['113', '114'])).
% 0.37/0.55  thf('116', plain,
% 0.37/0.55      (((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['112', '115'])).
% 0.37/0.55  thf('117', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('118', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.37/0.55      inference('demod', [status(thm)], ['101', '102'])).
% 0.37/0.55  thf('119', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['117', '118'])).
% 0.37/0.55  thf('120', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('121', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['113', '114'])).
% 0.37/0.55  thf('122', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('123', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.37/0.55  thf('124', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.55  thf('125', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.37/0.55      inference('demod', [status(thm)], ['123', '124'])).
% 0.37/0.55  thf('126', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['122', '125'])).
% 0.37/0.55  thf('127', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['89', '92'])).
% 0.37/0.55  thf('128', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('129', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['89', '92'])).
% 0.37/0.55  thf('130', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('131', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.55        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.55        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.37/0.55        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)],
% 0.37/0.55                ['109', '116', '119', '120', '121', '126', '127', '128', 
% 0.37/0.55                 '129', '130'])).
% 0.37/0.55  thf('132', plain,
% 0.37/0.55      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.37/0.55        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['131'])).
% 0.37/0.55  thf('133', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('134', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['85'])).
% 0.37/0.55  thf('135', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.55      inference('demod', [status(thm)], ['133', '134'])).
% 0.37/0.55  thf('136', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['132', '135'])).
% 0.37/0.55  thf('137', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf(dt_k6_partfun1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( m1_subset_1 @
% 0.37/0.55         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.37/0.55       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      (![X29 : $i]:
% 0.37/0.55         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 0.37/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.37/0.55  thf('139', plain,
% 0.37/0.55      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['137', '138'])).
% 0.37/0.55  thf('140', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.37/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.37/0.55  thf('141', plain,
% 0.37/0.55      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['139', '140'])).
% 0.37/0.55  thf('142', plain, ($false),
% 0.37/0.55      inference('demod', [status(thm)], ['56', '78', '86', '136', '141'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
