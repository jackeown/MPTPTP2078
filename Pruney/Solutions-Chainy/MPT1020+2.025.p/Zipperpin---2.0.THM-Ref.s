%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DeqGVINacb

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 (1628 expanded)
%              Number of leaves         :   46 ( 500 expanded)
%              Depth                    :   14
%              Number of atoms          : 1324 (42214 expanded)
%              Number of equality atoms :   97 ( 669 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_2 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
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
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','39','45'])).

thf('47',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X39 @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['59','60','61','64'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != X3 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X4
        = ( k6_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('67',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('68',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['59','60','61','64'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','75','76','77'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('82',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('83',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80','81','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X39 @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('93',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['88','89','90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('98',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['88','89','90','93'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('104',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('105',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X6: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X6 ) )
      = ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('108',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('110',plain,(
    ! [X6: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X6 ) )
      = ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf('112',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('113',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','85','105','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('117',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('119',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('120',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('122',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('123',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['114','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DeqGVINacb
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 119 iterations in 0.050s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.51  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(t87_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.51             ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.51             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51           ( ( r2_relset_1 @
% 0.21/0.51               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.51               ( k6_partfun1 @ A ) ) =>
% 0.21/0.51             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51            ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.51                ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.51                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51              ( ( r2_relset_1 @
% 0.21/0.51                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.51                  ( k6_partfun1 @ A ) ) =>
% 0.21/0.51                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X28 : $i, X29 : $i]:
% 0.21/0.51         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.21/0.51          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.21/0.51          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.21/0.51          | ~ (v1_funct_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.51        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.21/0.51        (k6_partfun1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t36_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.51           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.51               ( r2_relset_1 @
% 0.21/0.51                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.21/0.51                 ( k6_partfun1 @ A ) ) & 
% 0.21/0.51               ( v2_funct_1 @ C ) ) =>
% 0.21/0.51             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X35)
% 0.21/0.51          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.21/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.21/0.51          | ((X35) = (k2_funct_1 @ X38))
% 0.21/0.51          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 0.21/0.51               (k1_partfun1 @ X37 @ X36 @ X36 @ X37 @ X38 @ X35) @ 
% 0.21/0.51               (k6_partfun1 @ X37))
% 0.21/0.51          | ((X36) = (k1_xboole_0))
% 0.21/0.51          | ((X37) = (k1_xboole_0))
% 0.21/0.51          | ~ (v2_funct_1 @ X38)
% 0.21/0.51          | ((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.21/0.51          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.21/0.51          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.21/0.51          | ~ (v1_funct_1 @ X38))),
% 0.21/0.51      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.51          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.51          | ~ (v2_funct_1 @ X0)
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.51               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.51               (k6_partfun1 @ sk_A))
% 0.21/0.51          | ((sk_C_1) = (k2_funct_1 @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.51          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.51          | ~ (v2_funct_1 @ X0)
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.51               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.51               (k6_partfun1 @ sk_A))
% 0.21/0.51          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_C_1) = (k2_funct_1 @ X0))
% 0.21/0.51          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.51               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.51               (k6_partfun1 @ sk_A))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (v2_funct_1 @ X0)
% 0.21/0.51          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.51        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 0.21/0.51        | ~ (v2_funct_1 @ sk_B_1)
% 0.21/0.51        | ((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((sk_C_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.51         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X23)
% 0.21/0.51          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.21/0.51          | (v2_funct_2 @ X23 @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 0.21/0.51        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.51  thf(d3_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i]:
% 0.21/0.51         (~ (v2_funct_2 @ X27 @ X26)
% 0.21/0.51          | ((k2_relat_1 @ X27) = (X26))
% 0.21/0.51          | ~ (v5_relat_1 @ X27 @ X26)
% 0.21/0.51          | ~ (v1_relat_1 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.51        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 0.21/0.51        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X10 @ X12)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('37', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.21/0.51  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X23)
% 0.21/0.51          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 0.21/0.51          | (v2_funct_1 @ X23)
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((v2_funct_1 @ sk_B_1)
% 0.21/0.51        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((((sk_A) != (sk_A))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((sk_C_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((sk_C_1) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.51          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 0.21/0.51          | ((X19) != (X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '52'])).
% 0.21/0.51  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ 
% 0.21/0.51          (k2_funct_1 @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t67_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X39 : $i, X40 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X39 @ X39 @ X40) = (X39))
% 0.21/0.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.21/0.51          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 0.21/0.51          | ~ (v1_funct_1 @ X40))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_C_1)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.51        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60', '61', '64'])).
% 0.21/0.51  thf(t34_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.51         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X4) != (X3))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 0.21/0.51          | ((X4) = (k6_relat_1 @ X3))
% 0.21/0.51          | ~ (v1_funct_1 @ X4)
% 0.21/0.51          | ~ (v1_relat_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X4)
% 0.21/0.51          | ~ (v1_funct_1 @ X4)
% 0.21/0.51          | ((X4) = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.51  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.51  thf('68', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X4)
% 0.21/0.51          | ~ (v1_funct_1 @ X4)
% 0.21/0.51          | ((X4) = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.21/0.51      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.51        | ((sk_C_1) = (k6_partfun1 @ (k1_relat_1 @ sk_C_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('75', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('77', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60', '61', '64'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_A) | ((sk_C_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['72', '75', '76', '77'])).
% 0.21/0.51  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf('82', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.51  thf('83', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('84', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['78', '79', '80', '81', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (![X39 : $i, X40 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X39 @ X39 @ X40) = (X39))
% 0.21/0.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.21/0.51          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 0.21/0.51          | ~ (v1_funct_1 @ X40))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.51        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('90', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['88', '89', '90', '93'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('98', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('99', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['88', '89', '90', '93'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_A) | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.21/0.51  thf('101', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('104', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('105', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.21/0.51  thf('106', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf(t67_funct_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (![X6 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X6)) = (k6_relat_1 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.21/0.51  thf('108', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('109', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (![X6 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X6)) = (k6_partfun1 @ X6))),
% 0.21/0.51      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['106', '110'])).
% 0.21/0.51  thf('112', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('113', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['111', '112'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '85', '105', '113'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('117', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.51  thf('118', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('119', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '53'])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.21/0.51  thf('121', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.21/0.51  thf('122', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.21/0.51  thf('124', plain, ($false), inference('demod', [status(thm)], ['114', '123'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
