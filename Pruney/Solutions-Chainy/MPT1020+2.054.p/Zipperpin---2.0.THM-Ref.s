%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4hN3UxIQ2z

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:09 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  185 (1297 expanded)
%              Number of leaves         :   34 ( 394 expanded)
%              Depth                    :   19
%              Number of atoms          : 1532 (33582 expanded)
%              Number of equality atoms :   92 ( 436 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29
        = ( k2_funct_1 @ X32 ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X30 @ X30 @ X31 @ X32 @ X29 ) @ ( k6_partfun1 @ X31 ) )
      | ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    inference(demod,[status(thm)],['66','71','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','36','39'])).

thf(t197_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k2_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k2_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X5 = X4 )
      | ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t197_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    sk_C = sk_B ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','89'])).

thf('91',plain,(
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

thf('92',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('101',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X21 @ X22 ) @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('109',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['101','109','118'])).

thf('120',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('126',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('128',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('130',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('133',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['121','128','133'])).

thf('135',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('136',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('138',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('140',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_funct_1 @ sk_B )
    = sk_B ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['90','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('145',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('147',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('148',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['142','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4hN3UxIQ2z
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:53:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 381 iterations in 0.168s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.46/0.63  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.63  thf(t87_funct_2, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.46/0.63             ( v3_funct_2 @ C @ A @ A ) & 
% 0.46/0.63             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63           ( ( r2_relset_1 @
% 0.46/0.63               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.46/0.63               ( k6_partfun1 @ A ) ) =>
% 0.46/0.63             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.63            ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.63            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63          ( ![C:$i]:
% 0.46/0.63            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.46/0.63                ( v3_funct_2 @ C @ A @ A ) & 
% 0.46/0.63                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63              ( ( r2_relset_1 @
% 0.46/0.63                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.46/0.63                  ( k6_partfun1 @ A ) ) =>
% 0.46/0.63                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k2_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i]:
% 0.46/0.63         (((k2_funct_2 @ X24 @ X23) = (k2_funct_1 @ X23))
% 0.46/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.46/0.63          | ~ (v3_funct_2 @ X23 @ X24 @ X24)
% 0.46/0.63          | ~ (v1_funct_2 @ X23 @ X24 @ X24)
% 0.46/0.63          | ~ (v1_funct_1 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['0', '7'])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.46/0.63        (k6_partfun1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t36_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.63           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.46/0.63               ( r2_relset_1 @
% 0.46/0.63                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.63                 ( k6_partfun1 @ A ) ) & 
% 0.46/0.63               ( v2_funct_1 @ C ) ) =>
% 0.46/0.63             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.63               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X29)
% 0.46/0.63          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.46/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.46/0.63          | ((X29) = (k2_funct_1 @ X32))
% 0.46/0.63          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 0.46/0.63               (k1_partfun1 @ X31 @ X30 @ X30 @ X31 @ X32 @ X29) @ 
% 0.46/0.63               (k6_partfun1 @ X31))
% 0.46/0.63          | ((X30) = (k1_xboole_0))
% 0.46/0.63          | ((X31) = (k1_xboole_0))
% 0.46/0.63          | ~ (v2_funct_1 @ X32)
% 0.46/0.63          | ((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 0.46/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.46/0.63          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.46/0.63          | ~ (v1_funct_1 @ X32))),
% 0.46/0.63      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.63          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.46/0.63               (k6_partfun1 @ sk_A))
% 0.46/0.63          | ((sk_C) = (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.63          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.46/0.63               (k6_partfun1 @ sk_A))
% 0.46/0.63          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_C) = (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.46/0.63               (k6_partfun1 @ sk_A))
% 0.46/0.63          | ((sk_A) = (k1_xboole_0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.63        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_B)
% 0.46/0.63        | ((sk_A) = (k1_xboole_0))
% 0.46/0.63        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '16'])).
% 0.46/0.63  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.63         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X16)
% 0.46/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.63          | (v2_funct_2 @ X16 @ X18)
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (((v2_funct_2 @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.63  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.46/0.63  thf(d3_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.63       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (v2_funct_2 @ X20 @ X19)
% 0.46/0.63          | ((k2_relat_1 @ X20) = (X19))
% 0.46/0.63          | ~ (v5_relat_1 @ X20 @ X19)
% 0.46/0.63          | ~ (v1_relat_1 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.46/0.63        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.46/0.63        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.63          | (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf(fc6_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.63  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         ((v5_relat_1 @ X6 @ X8)
% 0.46/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('39', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.46/0.63  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X16)
% 0.46/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.63          | (v2_funct_1 @ X16)
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (((v2_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.63  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('47', plain, ((v2_funct_1 @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      ((((sk_A) != (sk_A))
% 0.46/0.63        | ((sk_A) = (k1_xboole_0))
% 0.46/0.63        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['0', '7'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.63          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.46/0.63          | ((X12) != (X15)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.63         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.63  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '54'])).
% 0.46/0.63  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X16)
% 0.46/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.63          | (v2_funct_2 @ X16 @ X18)
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (((v2_funct_2 @ sk_C @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.63  thf('62', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('64', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (v2_funct_2 @ X20 @ X19)
% 0.46/0.63          | ((k2_relat_1 @ X20) = (X19))
% 0.46/0.63          | ~ (v5_relat_1 @ X20 @ X19)
% 0.46/0.63          | ~ (v1_relat_1 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.46/0.63        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.63          | (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.63  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         ((v5_relat_1 @ X6 @ X8)
% 0.46/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.63  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['66', '71', '74'])).
% 0.46/0.63  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('77', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.63  thf('78', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.46/0.63  thf(t197_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( v1_relat_1 @ B ) =>
% 0.46/0.63           ( ( ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.46/0.63               ( ( k2_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.63             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X4)
% 0.46/0.63          | ((X5) = (X4))
% 0.46/0.63          | ((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.46/0.63          | ((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [t197_relat_1])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_A) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.63          | ((X0) = (sk_B))
% 0.46/0.63          | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.63  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((sk_A) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.63          | ((X0) = (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.63  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.63          | ((X0) = (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.63  thf('85', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((X0) = (sk_B))
% 0.46/0.63          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ((sk_C) = (sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['77', '85'])).
% 0.46/0.63  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.63  thf('88', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.63  thf('89', plain, (((sk_C) = (sk_B))),
% 0.46/0.63      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.63  thf('90', plain,
% 0.46/0.63      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['58', '89'])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k2_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.63       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.46/0.63         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.46/0.63         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.46/0.63         ( m1_subset_1 @
% 0.46/0.63           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.46/0.63  thf('92', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.46/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.46/0.63          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_1 @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.63  thf('93', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.63  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('95', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('96', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('97', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.46/0.63  thf('98', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['97', '98'])).
% 0.46/0.63  thf('100', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ X16)
% 0.46/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.63          | (v2_funct_2 @ X16 @ X18)
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.63  thf('101', plain,
% 0.46/0.63      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('103', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         ((v3_funct_2 @ (k2_funct_2 @ X21 @ X22) @ X21 @ X21)
% 0.46/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.46/0.63          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_1 @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.63  thf('104', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.63  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('106', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('107', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('108', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('109', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.46/0.63  thf('110', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('111', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 0.46/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.46/0.63          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.46/0.63          | ~ (v1_funct_1 @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.63  thf('112', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.46/0.63        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.63  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('114', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('115', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('116', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.46/0.63  thf('117', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.63  thf('119', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['101', '109', '118'])).
% 0.46/0.63  thf('120', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (v2_funct_2 @ X20 @ X19)
% 0.46/0.63          | ((k2_relat_1 @ X20) = (X19))
% 0.46/0.63          | ~ (v5_relat_1 @ X20 @ X19)
% 0.46/0.63          | ~ (v1_relat_1 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.46/0.63        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.46/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['119', '120'])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.46/0.63  thf('123', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.63          | (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.63  thf('124', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.46/0.63        | (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.63  thf('125', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.63  thf('126', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['124', '125'])).
% 0.46/0.63  thf('127', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('128', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['126', '127'])).
% 0.46/0.63  thf('129', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.46/0.63  thf('130', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         ((v5_relat_1 @ X6 @ X8)
% 0.46/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('131', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.63  thf('132', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.46/0.63  thf('133', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['131', '132'])).
% 0.46/0.63  thf('134', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['121', '128', '133'])).
% 0.46/0.63  thf('135', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('136', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.63  thf('137', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((X0) = (sk_B))
% 0.46/0.63          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.63  thf('138', plain,
% 0.46/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.46/0.63        | ((k2_funct_1 @ sk_B) = (sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.63  thf('139', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['126', '127'])).
% 0.46/0.63  thf('140', plain,
% 0.46/0.63      ((((k1_xboole_0) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B) = (sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['138', '139'])).
% 0.46/0.63  thf('141', plain, (((k2_funct_1 @ sk_B) = (sk_B))),
% 0.46/0.63      inference('simplify', [status(thm)], ['140'])).
% 0.46/0.63  thf('142', plain,
% 0.46/0.63      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['90', '141'])).
% 0.46/0.63  thf('143', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('144', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.63         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.63  thf('145', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['143', '144'])).
% 0.46/0.63  thf('146', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('147', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['51', '55'])).
% 0.46/0.63  thf('148', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.46/0.63  thf('149', plain, ($false), inference('demod', [status(thm)], ['142', '148'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
