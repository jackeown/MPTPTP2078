%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zo00rPjee1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 868 expanded)
%              Number of leaves         :   43 ( 277 expanded)
%              Depth                    :   16
%              Number of atoms          : 1448 (19146 expanded)
%              Number of equality atoms :  122 ( 401 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

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
    ! [X31: $i,X32: $i] :
      ( ( ( k2_funct_2 @ X32 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38
        = ( k2_funct_1 @ X41 ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38 ) @ ( k6_partfun1 @ X40 ) )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','36','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','41','47'])).

thf('49',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('58',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('61',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['66','71','74'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('77',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('79',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

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
    inference(demod,[status(thm)],['31','36','39'])).

thf('84',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

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
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('92',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('97',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('104',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('105',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

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

thf('110',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X13 @ X12 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('111',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X13 @ X12 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('115',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('116',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('117',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('118',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('120',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('121',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k6_partfun1 @ k1_xboole_0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['100','123'])).

thf('125',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('126',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('130',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('133',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('134',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('136',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['58','82','90','131','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zo00rPjee1
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 146 iterations in 0.057s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.22/0.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.22/0.52  thf(t87_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.22/0.52             ( v3_funct_2 @ C @ A @ A ) & 
% 0.22/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52           ( ( r2_relset_1 @
% 0.22/0.52               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.22/0.52               ( k6_partfun1 @ A ) ) =>
% 0.22/0.52             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52            ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52          ( ![C:$i]:
% 0.22/0.52            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.22/0.52                ( v3_funct_2 @ C @ A @ A ) & 
% 0.22/0.52                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52              ( ( r2_relset_1 @
% 0.22/0.52                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.22/0.52                  ( k6_partfun1 @ A ) ) =>
% 0.22/0.52                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k2_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X31 : $i, X32 : $i]:
% 0.22/0.52         (((k2_funct_2 @ X32 @ X31) = (k2_funct_1 @ X31))
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.22/0.52          | ~ (v3_funct_2 @ X31 @ X32 @ X32)
% 0.22/0.52          | ~ (v1_funct_2 @ X31 @ X32 @ X32)
% 0.22/0.52          | ~ (v1_funct_1 @ X31))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.22/0.52  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.52        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52        (k6_partfun1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t36_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.22/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.22/0.52           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.22/0.52               ( r2_relset_1 @
% 0.22/0.52                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.22/0.52                 ( k6_partfun1 @ A ) ) & 
% 0.22/0.52               ( v2_funct_1 @ C ) ) =>
% 0.22/0.52             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X38)
% 0.22/0.52          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.22/0.52          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.22/0.52          | ((X38) = (k2_funct_1 @ X41))
% 0.22/0.52          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 0.22/0.52               (k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38) @ 
% 0.22/0.52               (k6_partfun1 @ X40))
% 0.22/0.52          | ((X39) = (k1_xboole_0))
% 0.22/0.52          | ((X40) = (k1_xboole_0))
% 0.22/0.52          | ~ (v2_funct_1 @ X41)
% 0.22/0.52          | ((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 0.22/0.52          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.22/0.52          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.22/0.52          | ~ (v1_funct_1 @ X41))),
% 0.22/0.52      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.52               (k6_partfun1 @ sk_A))
% 0.22/0.52          | ((sk_C) = (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.52               (k6_partfun1 @ sk_A))
% 0.22/0.52          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((sk_C) = (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.22/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.52               (k6_partfun1 @ sk_A))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_B)
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.52  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.52         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.22/0.52          | (v2_funct_2 @ X24 @ X26)
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((v2_funct_2 @ sk_B @ sk_A)
% 0.22/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.52  thf(d3_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i]:
% 0.22/0.52         (~ (v2_funct_2 @ X28 @ X27)
% 0.22/0.52          | ((k2_relat_1 @ X28) = (X27))
% 0.22/0.52          | ~ (v5_relat_1 @ X28 @ X27)
% 0.22/0.52          | ~ (v1_relat_1 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.22/0.52        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.52          | (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         ((v5_relat_1 @ X14 @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('39', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.22/0.52  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.22/0.52          | (v2_funct_1 @ X24)
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B)
% 0.22/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((((sk_A) != (sk_A))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.22/0.52          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.22/0.52          | ((X20) != (X23)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.52         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.52  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '54'])).
% 0.22/0.52  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '55'])).
% 0.22/0.52  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '55'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.22/0.52          | (v2_funct_2 @ X24 @ X26)
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (((v2_funct_2 @ sk_C @ sk_A)
% 0.22/0.52        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.52  thf('62', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('64', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i]:
% 0.22/0.52         (~ (v2_funct_2 @ X28 @ X27)
% 0.22/0.52          | ((k2_relat_1 @ X28) = (X27))
% 0.22/0.52          | ~ (v5_relat_1 @ X28 @ X27)
% 0.22/0.52          | ~ (v1_relat_1 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.22/0.52        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.52          | (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.52  thf('72', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('73', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         ((v5_relat_1 @ X14 @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.52  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['66', '71', '74'])).
% 0.22/0.52  thf(t64_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X4 : $i]:
% 0.22/0.52         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.22/0.52          | ((X4) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      ((((sk_A) != (k1_xboole_0))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.52  thf('79', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.52  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '55'])).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['79', '80'])).
% 0.22/0.52  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['81'])).
% 0.22/0.52  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      (![X4 : $i]:
% 0.22/0.52         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.22/0.52          | ((X4) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      ((((sk_A) != (k1_xboole_0))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.52  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('87', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['85', '86'])).
% 0.22/0.52  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '55'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.52  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['89'])).
% 0.22/0.52  thf(t71_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.52  thf('91', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.52  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.52  thf('92', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('93', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.22/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (![X4 : $i]:
% 0.22/0.52         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 0.22/0.52          | ((X4) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((X0) != (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.52  thf(fc4_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.52  thf('96', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.52  thf('97', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('98', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('99', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['95', '98'])).
% 0.22/0.52  thf('100', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['99'])).
% 0.22/0.52  thf('101', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.52  thf('102', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('103', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.22/0.52      inference('demod', [status(thm)], ['101', '102'])).
% 0.22/0.52  thf(t80_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      (![X7 : $i]:
% 0.22/0.52         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.22/0.52  thf('105', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('106', plain,
% 0.22/0.52      (![X7 : $i]:
% 0.22/0.52         (((k5_relat_1 @ X7 @ (k6_partfun1 @ (k2_relat_1 @ X7))) = (X7))
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('demod', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf('107', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.22/0.52            = (k6_partfun1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['103', '106'])).
% 0.22/0.52  thf('108', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('109', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.22/0.52           = (k6_partfun1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.52  thf(t63_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52           ( ( ( v2_funct_1 @ A ) & 
% 0.22/0.52               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.22/0.52               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.22/0.52             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('110', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X12)
% 0.22/0.52          | ~ (v1_funct_1 @ X12)
% 0.22/0.52          | ((X12) = (k2_funct_1 @ X13))
% 0.22/0.52          | ((k5_relat_1 @ X13 @ X12) != (k6_relat_1 @ (k1_relat_1 @ X13)))
% 0.22/0.52          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X12))
% 0.22/0.52          | ~ (v2_funct_1 @ X13)
% 0.22/0.52          | ~ (v1_funct_1 @ X13)
% 0.22/0.52          | ~ (v1_relat_1 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.22/0.52  thf('111', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X12)
% 0.22/0.52          | ~ (v1_funct_1 @ X12)
% 0.22/0.52          | ((X12) = (k2_funct_1 @ X13))
% 0.22/0.52          | ((k5_relat_1 @ X13 @ X12) != (k6_partfun1 @ (k1_relat_1 @ X13)))
% 0.22/0.52          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X12))
% 0.22/0.52          | ~ (v2_funct_1 @ X13)
% 0.22/0.52          | ~ (v1_funct_1 @ X13)
% 0.22/0.52          | ~ (v1_relat_1 @ X13))),
% 0.22/0.52      inference('demod', [status(thm)], ['110', '111'])).
% 0.22/0.52  thf('113', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k6_partfun1 @ X0)
% 0.22/0.52            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.52              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 0.22/0.52          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['109', '112'])).
% 0.22/0.52  thf('114', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.22/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.22/0.52  thf('115', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('116', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.52  thf('117', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.52  thf('118', plain, (![X9 : $i]: (v2_funct_1 @ (k6_partfun1 @ X9))),
% 0.22/0.52      inference('demod', [status(thm)], ['116', '117'])).
% 0.22/0.52  thf('119', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.22/0.52      inference('demod', [status(thm)], ['101', '102'])).
% 0.22/0.52  thf('120', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.22/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.22/0.52  thf('121', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('122', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.52          | ((X0) != (X0))
% 0.22/0.52          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['113', '114', '115', '118', '119', '120', '121'])).
% 0.22/0.52  thf('123', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['122'])).
% 0.22/0.52  thf('124', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.52        | ((k6_partfun1 @ k1_xboole_0)
% 0.22/0.52            = (k2_funct_1 @ (k6_partfun1 @ k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['100', '123'])).
% 0.22/0.52  thf('125', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['99'])).
% 0.22/0.52  thf('126', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['99'])).
% 0.22/0.52  thf('127', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.52        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.22/0.52  thf('128', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('129', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['89'])).
% 0.22/0.52  thf('130', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['128', '129'])).
% 0.22/0.52  thf('131', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['127', '130'])).
% 0.22/0.52  thf('132', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['99'])).
% 0.22/0.52  thf(dt_k6_partfun1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( m1_subset_1 @
% 0.22/0.52         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.52       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.22/0.52  thf('133', plain,
% 0.22/0.52      (![X30 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.22/0.52  thf('134', plain,
% 0.22/0.52      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['132', '133'])).
% 0.22/0.52  thf('135', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.52         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.52  thf('136', plain,
% 0.22/0.52      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['134', '135'])).
% 0.22/0.52  thf('137', plain, ($false),
% 0.22/0.52      inference('demod', [status(thm)], ['58', '82', '90', '131', '136'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
