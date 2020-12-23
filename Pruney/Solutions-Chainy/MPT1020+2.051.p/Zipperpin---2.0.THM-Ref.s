%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tFkodDYxtc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  177 (1676 expanded)
%              Number of leaves         :   47 ( 516 expanded)
%              Depth                    :   14
%              Number of atoms          : 1348 (42438 expanded)
%              Number of equality atoms :   97 ( 669 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( X36
        = ( k2_funct_1 @ X39 ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X37 @ X37 @ X38 @ X39 @ X36 ) @ ( k6_partfun1 @ X38 ) )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['31','36','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','41','47'])).

thf('49',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('58',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('60',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X40 @ X41 )
        = X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['61','62','63','66'])).

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

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != X7 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 )
      | ( X8
        = ( k6_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('69',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( r2_hidden @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('70',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( r2_hidden @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf('82',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','79','80','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('86',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84','85','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X40 @ X41 )
        = X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('102',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94','97'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('108',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('109',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('111',plain,(
    ! [X10: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X10 ) )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('112',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('114',plain,(
    ! [X10: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','114'])).

thf('116',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('117',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','89','109','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('121',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('123',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('124',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('126',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('127',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['118','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tFkodDYxtc
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 127 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.21/0.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
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
% 0.21/0.50      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.21/0.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.50          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.21/0.50          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.21/0.50          | ~ (v1_funct_1 @ X29))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.21/0.50        (k6_partfun1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
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
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X36)
% 0.21/0.50          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.21/0.50          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.21/0.50          | ((X36) = (k2_funct_1 @ X39))
% 0.21/0.50          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.21/0.50               (k1_partfun1 @ X38 @ X37 @ X37 @ X38 @ X39 @ X36) @ 
% 0.21/0.50               (k6_partfun1 @ X38))
% 0.21/0.50          | ((X37) = (k1_xboole_0))
% 0.21/0.50          | ((X38) = (k1_xboole_0))
% 0.21/0.50          | ~ (v2_funct_1 @ X39)
% 0.21/0.50          | ((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.21/0.50          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.21/0.50          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.21/0.50          | ~ (v1_funct_1 @ X39))),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.50               (k6_partfun1 @ sk_A))
% 0.21/0.50          | ((sk_C_1) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.50               (k6_partfun1 @ sk_A))
% 0.21/0.50          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_C_1) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 0.21/0.50               (k6_partfun1 @ sk_A))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 0.21/0.50        | ~ (v2_funct_1 @ sk_B_1)
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.50  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.50         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X24)
% 0.21/0.50          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.50          | (v2_funct_2 @ X24 @ X26)
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.50  thf(d3_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i]:
% 0.21/0.50         (~ (v2_funct_2 @ X28 @ X27)
% 0.21/0.50          | ((k2_relat_1 @ X28) = (X27))
% 0.21/0.50          | ~ (v5_relat_1 @ X28 @ X27)
% 0.21/0.50          | ~ (v1_relat_1 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 0.21/0.50        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.50          | (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('36', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('39', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.21/0.50  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X24)
% 0.21/0.50          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.50          | (v2_funct_1 @ X24)
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((((sk_A) != (sk_A))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C_1) = (k2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((((sk_C_1) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.50          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.21/0.50          | ((X20) != (X23)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.50  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '54'])).
% 0.21/0.50  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ 
% 0.21/0.50          (k2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t67_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X40 : $i, X41 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X40 @ X40 @ X41) = (X40))
% 0.21/0.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.21/0.50          | ~ (v1_funct_2 @ X41 @ X40 @ X40)
% 0.21/0.50          | ~ (v1_funct_1 @ X41))),
% 0.21/0.50      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.50        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.21/0.50  thf(t34_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.50         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X8) != (X7))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X8 @ X7) @ X7)
% 0.21/0.50          | ((X8) = (k6_relat_1 @ X7))
% 0.21/0.50          | ~ (v1_funct_1 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (![X8 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X8)
% 0.21/0.50          | ((X8) = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X8 @ (k1_relat_1 @ X8)) @ (k1_relat_1 @ X8)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('70', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (![X8 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X8)
% 0.21/0.50          | ((X8) = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X8 @ (k1_relat_1 @ X8)) @ (k1_relat_1 @ X8)))),
% 0.21/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_A)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50        | ((sk_C_1) = (k6_partfun1 @ (k1_relat_1 @ sk_C_1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['67', '73'])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.50          | (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('79', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.50  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('81', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_A) | ((sk_C_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '79', '80', '81'])).
% 0.21/0.50  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.50  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.50  thf('86', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.50  thf('87', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('88', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('89', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['82', '83', '84', '85', '88'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X40 : $i, X41 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X40 @ X40 @ X41) = (X40))
% 0.21/0.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.21/0.50          | ~ (v1_funct_2 @ X41 @ X40 @ X40)
% 0.21/0.50          | ~ (v1_funct_1 @ X41))),
% 0.21/0.50      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('94', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('97', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.50  thf('98', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['92', '93', '94', '97'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_A)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.50  thf('101', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('102', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('103', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['92', '93', '94', '97'])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_A) | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.21/0.50  thf('105', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('108', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('109', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.21/0.50  thf('110', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf(t67_funct_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('111', plain,
% 0.21/0.50      (![X10 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.21/0.50  thf('112', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('113', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('114', plain,
% 0.21/0.50      (![X10 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 0.21/0.50      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.21/0.50  thf('115', plain,
% 0.21/0.50      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['110', '114'])).
% 0.21/0.50  thf('116', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('117', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['115', '116'])).
% 0.21/0.50  thf('118', plain,
% 0.21/0.50      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '89', '109', '117'])).
% 0.21/0.50  thf('119', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('120', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.50  thf('121', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['119', '120'])).
% 0.21/0.50  thf('122', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('123', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.50  thf('124', plain,
% 0.21/0.50      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.21/0.50  thf('125', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.21/0.50  thf('126', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.21/0.50  thf('127', plain,
% 0.21/0.50      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.21/0.50  thf('128', plain, ($false), inference('demod', [status(thm)], ['118', '127'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
