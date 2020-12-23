%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bny0Ba2GS4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  164 (1307 expanded)
%              Number of leaves         :   43 ( 403 expanded)
%              Depth                    :   13
%              Number of atoms          : 1215 (31727 expanded)
%              Number of equality atoms :   91 ( 565 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_partfun1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_2 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_2 @ X32 @ X31 )
      | ( ( k2_relat_1 @ X32 )
        = X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('80',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('81',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('82',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('84',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['77','80','87'])).

thf('89',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('92',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['63','64','65','67','88','89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('100',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['77','80','87'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('105',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X17: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X17 ) )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('108',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('110',plain,(
    ! [X17: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X17 ) )
      = ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf('112',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('113',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['77','80','87'])).

thf('115',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['58','92','105','113','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bny0Ba2GS4
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 247 iterations in 0.108s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.36/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.36/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.36/0.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.53  thf(t87_funct_2, conjecture,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.36/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.53       ( ![C:$i]:
% 0.36/0.53         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.53             ( v3_funct_2 @ C @ A @ A ) & 
% 0.36/0.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.53           ( ( r2_relset_1 @
% 0.36/0.53               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.36/0.53               ( k6_partfun1 @ A ) ) =>
% 0.36/0.53             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i]:
% 0.36/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.53            ( v3_funct_2 @ B @ A @ A ) & 
% 0.36/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.53          ( ![C:$i]:
% 0.36/0.53            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.53                ( v3_funct_2 @ C @ A @ A ) & 
% 0.36/0.53                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.53              ( ( r2_relset_1 @
% 0.36/0.53                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.36/0.53                  ( k6_partfun1 @ A ) ) =>
% 0.36/0.53                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k2_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.36/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.53       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (![X33 : $i, X34 : $i]:
% 0.36/0.53         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 0.36/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.36/0.53          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 0.36/0.53          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 0.36/0.53          | ~ (v1_funct_1 @ X33))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.36/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.53        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.53  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.36/0.53  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.53        (k6_partfun1 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t36_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.53       ( ![D:$i]:
% 0.36/0.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.36/0.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.36/0.53           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.36/0.53               ( r2_relset_1 @
% 0.36/0.53                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.36/0.53                 ( k6_partfun1 @ A ) ) & 
% 0.36/0.53               ( v2_funct_1 @ C ) ) =>
% 0.36/0.53             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.53               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.53         (~ (v1_funct_1 @ X40)
% 0.36/0.53          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.36/0.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.36/0.53          | ((X40) = (k2_funct_1 @ X43))
% 0.36/0.53          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.36/0.53               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 0.36/0.53               (k6_partfun1 @ X42))
% 0.36/0.53          | ((X41) = (k1_xboole_0))
% 0.36/0.53          | ((X42) = (k1_xboole_0))
% 0.36/0.53          | ~ (v2_funct_1 @ X43)
% 0.36/0.53          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 0.36/0.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.36/0.53          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.36/0.53          | ~ (v1_funct_1 @ X43))),
% 0.36/0.53      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_funct_1 @ X0)
% 0.36/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.36/0.53          | ~ (v2_funct_1 @ X0)
% 0.36/0.53          | ((sk_A) = (k1_xboole_0))
% 0.36/0.53          | ((sk_A) = (k1_xboole_0))
% 0.36/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.36/0.53               (k6_partfun1 @ sk_A))
% 0.36/0.53          | ((sk_C) = (k2_funct_1 @ X0))
% 0.36/0.53          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.36/0.53          | ~ (v1_funct_1 @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.53  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_funct_1 @ X0)
% 0.36/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.36/0.53          | ~ (v2_funct_1 @ X0)
% 0.36/0.53          | ((sk_A) = (k1_xboole_0))
% 0.36/0.53          | ((sk_A) = (k1_xboole_0))
% 0.36/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.36/0.53               (k6_partfun1 @ sk_A))
% 0.36/0.53          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.36/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (((sk_C) = (k2_funct_1 @ X0))
% 0.36/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.36/0.53               (k6_partfun1 @ sk_A))
% 0.36/0.53          | ((sk_A) = (k1_xboole_0))
% 0.36/0.53          | ~ (v2_funct_1 @ X0)
% 0.36/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.36/0.53          | ~ (v1_funct_1 @ X0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.36/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.53        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.53        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.36/0.53        | ~ (v2_funct_1 @ sk_B)
% 0.36/0.53        | ((sk_A) = (k1_xboole_0))
% 0.36/0.53        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['9', '16'])).
% 0.36/0.53  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.53         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.36/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc2_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.36/0.53         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.53         (~ (v1_funct_1 @ X28)
% 0.36/0.53          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 0.36/0.53          | (v2_funct_2 @ X28 @ X30)
% 0.36/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      (((v2_funct_2 @ sk_B @ sk_A)
% 0.36/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.53        | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.53  thf(d3_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.36/0.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      (![X31 : $i, X32 : $i]:
% 0.36/0.53         (~ (v2_funct_2 @ X32 @ X31)
% 0.36/0.53          | ((k2_relat_1 @ X32) = (X31))
% 0.36/0.53          | ~ (v5_relat_1 @ X32 @ X31)
% 0.36/0.53          | ~ (v1_relat_1 @ X32))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.53        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.36/0.53        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc2_relat_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      (![X9 : $i, X10 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.36/0.53          | (v1_relat_1 @ X9)
% 0.36/0.53          | ~ (v1_relat_1 @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.53  thf('34', plain,
% 0.36/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.53  thf(fc6_relat_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.53  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.53  thf('37', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc2_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.53         ((v5_relat_1 @ X18 @ X20)
% 0.36/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.53  thf('39', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.36/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.53  thf('40', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.36/0.53  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['23', '40'])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.53         (~ (v1_funct_1 @ X28)
% 0.36/0.53          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 0.36/0.53          | (v2_funct_1 @ X28)
% 0.36/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (((v2_funct_1 @ sk_B)
% 0.36/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.53        | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.53  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('47', plain, ((v2_funct_1 @ sk_B)),
% 0.36/0.53      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      ((((sk_A) != (sk_A))
% 0.36/0.53        | ((sk_A) = (k1_xboole_0))
% 0.36/0.53        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.53  thf('53', plain,
% 0.36/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.36/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.36/0.53          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 0.36/0.53          | ((X24) != (X27)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.53  thf('54', plain,
% 0.36/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.53         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 0.36/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.36/0.53  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.36/0.53      inference('sup-', [status(thm)], ['52', '54'])).
% 0.36/0.53  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('58', plain,
% 0.36/0.53      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.36/0.53  thf('59', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t3_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('60', plain,
% 0.36/0.53      (![X6 : $i, X7 : $i]:
% 0.36/0.53         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('61', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.53  thf(d10_xboole_0, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      (![X0 : $i, X2 : $i]:
% 0.36/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 0.36/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.53  thf('64', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf(t113_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.53  thf('66', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i]:
% 0.36/0.53         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('68', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('69', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.36/0.53  thf('71', plain,
% 0.36/0.53      (![X6 : $i, X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('72', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.53  thf('73', plain,
% 0.36/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.53         ((v5_relat_1 @ X18 @ X20)
% 0.36/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.53  thf('74', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 0.36/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.53  thf('75', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.36/0.53      inference('sup+', [status(thm)], ['68', '74'])).
% 0.36/0.53  thf(d19_relat_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ B ) =>
% 0.36/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.53  thf('76', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         (~ (v5_relat_1 @ X11 @ X12)
% 0.36/0.53          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.36/0.53          | ~ (v1_relat_1 @ X11))),
% 0.36/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.53  thf('77', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.53          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.53  thf('78', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('79', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.53  thf('80', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.53      inference('sup+', [status(thm)], ['78', '79'])).
% 0.36/0.53  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.53  thf('81', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.53  thf(redefinition_k6_partfun1, axiom,
% 0.36/0.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.53  thf('82', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.53  thf('83', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.53  thf(t71_relat_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.53  thf('84', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.36/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.53  thf('85', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.53  thf('86', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.36/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.36/0.53  thf('87', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['83', '86'])).
% 0.36/0.53  thf('88', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.53      inference('demod', [status(thm)], ['77', '80', '87'])).
% 0.36/0.53  thf('89', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('91', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('92', plain, (((k1_xboole_0) = (sk_C))),
% 0.36/0.53      inference('demod', [status(thm)],
% 0.36/0.53                ['63', '64', '65', '67', '88', '89', '90', '91'])).
% 0.36/0.53  thf('93', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('94', plain,
% 0.36/0.53      (![X6 : $i, X7 : $i]:
% 0.36/0.53         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('95', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.53  thf('96', plain,
% 0.36/0.53      (![X0 : $i, X2 : $i]:
% 0.36/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('97', plain,
% 0.36/0.53      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 0.36/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.53  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('100', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('101', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.53      inference('demod', [status(thm)], ['77', '80', '87'])).
% 0.36/0.53  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['51', '55'])).
% 0.36/0.53  thf('104', plain,
% 0.36/0.53      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.53  thf('105', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.53      inference('demod', [status(thm)],
% 0.36/0.53                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.36/0.53  thf('106', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.53  thf(t67_funct_1, axiom,
% 0.36/0.53    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.53  thf('107', plain,
% 0.36/0.53      (![X17 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X17)) = (k6_relat_1 @ X17))),
% 0.36/0.53      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.36/0.53  thf('108', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.53  thf('109', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.53  thf('110', plain,
% 0.36/0.53      (![X17 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X17)) = (k6_partfun1 @ X17))),
% 0.36/0.53      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.36/0.53  thf('111', plain,
% 0.36/0.53      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['106', '110'])).
% 0.36/0.53  thf('112', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.53  thf('113', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['111', '112'])).
% 0.36/0.53  thf('114', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.53      inference('demod', [status(thm)], ['77', '80', '87'])).
% 0.36/0.53  thf('115', plain,
% 0.36/0.53      (![X6 : $i, X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('116', plain,
% 0.36/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.53  thf('117', plain,
% 0.36/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.53         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 0.36/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.36/0.53  thf('118', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.53      inference('sup-', [status(thm)], ['116', '117'])).
% 0.36/0.53  thf('119', plain, ($false),
% 0.36/0.53      inference('demod', [status(thm)], ['58', '92', '105', '113', '118'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
