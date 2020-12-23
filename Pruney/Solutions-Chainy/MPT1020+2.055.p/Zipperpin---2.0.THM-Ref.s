%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0smatvxJ1s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:09 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  191 (1617 expanded)
%              Number of leaves         :   35 ( 489 expanded)
%              Depth                    :   17
%              Number of atoms          : 1538 (41282 expanded)
%              Number of equality atoms :   95 ( 557 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X22: $i,X23: $i] :
      ( ( ( k2_funct_2 @ X23 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24
        = ( k2_funct_1 @ X27 ) )
      | ~ ( r2_relset_1 @ X26 @ X26 @ ( k1_partfun1 @ X26 @ X25 @ X25 @ X26 @ X27 @ X24 ) @ ( k6_partfun1 @ X26 ) )
      | ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('99',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('109',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('110',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X20 @ X21 ) @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('118',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['110','118'])).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('136',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('138',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('140',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_funct_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('143',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','82','90','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('147',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('149',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('150',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('152',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('153',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['144','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0smatvxJ1s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 317 iterations in 0.162s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.41/0.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.41/0.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.41/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.62  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.62  thf(t87_funct_2, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( v3_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.41/0.62             ( v3_funct_2 @ C @ A @ A ) & 
% 0.41/0.62             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62           ( ( r2_relset_1 @
% 0.41/0.62               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.41/0.62               ( k6_partfun1 @ A ) ) =>
% 0.41/0.62             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62            ( v3_funct_2 @ B @ A @ A ) & 
% 0.41/0.62            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62          ( ![C:$i]:
% 0.41/0.62            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.41/0.62                ( v3_funct_2 @ C @ A @ A ) & 
% 0.41/0.62                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62              ( ( r2_relset_1 @
% 0.41/0.62                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.41/0.62                  ( k6_partfun1 @ A ) ) =>
% 0.41/0.62                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k2_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( v3_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i]:
% 0.41/0.62         (((k2_funct_2 @ X23 @ X22) = (k2_funct_1 @ X22))
% 0.41/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))
% 0.41/0.62          | ~ (v3_funct_2 @ X22 @ X23 @ X23)
% 0.41/0.62          | ~ (v1_funct_2 @ X22 @ X23 @ X23)
% 0.41/0.62          | ~ (v1_funct_1 @ X22))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.62        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.62        (k6_partfun1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t36_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ![D:$i]:
% 0.41/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.41/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.41/0.62           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.41/0.62               ( r2_relset_1 @
% 0.41/0.62                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.41/0.62                 ( k6_partfun1 @ A ) ) & 
% 0.41/0.62               ( v2_funct_1 @ C ) ) =>
% 0.41/0.62             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X24)
% 0.41/0.62          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.41/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.62          | ((X24) = (k2_funct_1 @ X27))
% 0.41/0.62          | ~ (r2_relset_1 @ X26 @ X26 @ 
% 0.41/0.62               (k1_partfun1 @ X26 @ X25 @ X25 @ X26 @ X27 @ X24) @ 
% 0.41/0.62               (k6_partfun1 @ X26))
% 0.41/0.62          | ((X25) = (k1_xboole_0))
% 0.41/0.62          | ((X26) = (k1_xboole_0))
% 0.41/0.62          | ~ (v2_funct_1 @ X27)
% 0.41/0.62          | ((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.41/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.41/0.62          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.41/0.62          | ~ (v1_funct_1 @ X27))),
% 0.41/0.62      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.41/0.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ((sk_A) = (k1_xboole_0))
% 0.41/0.62          | ((sk_A) = (k1_xboole_0))
% 0.41/0.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.41/0.62               (k6_partfun1 @ sk_A))
% 0.41/0.62          | ((sk_C) = (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.41/0.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ((sk_A) = (k1_xboole_0))
% 0.41/0.62          | ((sk_A) = (k1_xboole_0))
% 0.41/0.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.41/0.62               (k6_partfun1 @ sk_A))
% 0.41/0.62          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((sk_C) = (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.41/0.62               (k6_partfun1 @ sk_A))
% 0.41/0.62          | ((sk_A) = (k1_xboole_0))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.41/0.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.41/0.62          | ~ (v1_funct_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.41/0.62        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.41/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.41/0.62        | ((sk_A) = (k1_xboole_0))
% 0.41/0.62        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['9', '16'])).
% 0.41/0.62  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.41/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc2_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.41/0.62         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.41/0.62          | (v2_funct_2 @ X15 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (((v2_funct_2 @ sk_B @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.41/0.62  thf(d3_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (v2_funct_2 @ X19 @ X18)
% 0.41/0.62          | ((k2_relat_1 @ X19) = (X18))
% 0.41/0.62          | ~ (v5_relat_1 @ X19 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.41/0.62        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc2_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.62          | (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.62  thf(fc6_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.62  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((v5_relat_1 @ X5 @ X7)
% 0.41/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.62  thf('39', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.41/0.62  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.41/0.62          | (v2_funct_1 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (((v2_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.62  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('47', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      ((((sk_A) != (sk_A))
% 0.41/0.62        | ((sk_A) = (k1_xboole_0))
% 0.41/0.62        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '7'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_r2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.41/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.41/0.62          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 0.41/0.62          | ((X11) != (X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.62         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.41/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.41/0.62  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['52', '54'])).
% 0.41/0.62  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.41/0.62          | (v2_funct_2 @ X15 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.41/0.62  thf('61', plain,
% 0.41/0.62      (((v2_funct_2 @ sk_C @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.41/0.62  thf('62', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('64', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.41/0.62  thf('65', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (v2_funct_2 @ X19 @ X18)
% 0.41/0.62          | ((k2_relat_1 @ X19) = (X18))
% 0.41/0.62          | ~ (v5_relat_1 @ X19 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.41/0.62        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.62  thf('67', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('68', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.62          | (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.62  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.41/0.62  thf('72', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((v5_relat_1 @ X5 @ X7)
% 0.41/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.62  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['66', '71', '74'])).
% 0.41/0.62  thf(t64_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.62  thf('76', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.41/0.62          | ((X4) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.41/0.62  thf('77', plain,
% 0.41/0.62      ((((sk_A) != (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.62  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.41/0.62  thf('79', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['77', '78'])).
% 0.41/0.62  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('81', plain,
% 0.41/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['81'])).
% 0.41/0.62  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.41/0.62          | ((X4) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.41/0.62  thf('85', plain,
% 0.41/0.62      ((((sk_A) != (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.41/0.62  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('87', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.41/0.62  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('89', plain,
% 0.41/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['87', '88'])).
% 0.41/0.62  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.41/0.62  thf('91', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k2_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( v3_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.41/0.62         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.41/0.62         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.41/0.62         ( m1_subset_1 @
% 0.41/0.62           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.41/0.62  thf('92', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k2_funct_2 @ X20 @ X21) @ 
% 0.41/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.41/0.62          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_1 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.41/0.62  thf('93', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.41/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['91', '92'])).
% 0.41/0.62  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('95', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('96', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('97', plain,
% 0.41/0.62      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.41/0.62  thf('98', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.62         (~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.41/0.62          | (v2_funct_2 @ X15 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.41/0.62  thf('99', plain,
% 0.41/0.62      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.41/0.62  thf('100', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('101', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k2_funct_2 @ X20 @ X21))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.41/0.62          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_1 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.41/0.62  thf('102', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.41/0.62  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('104', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('105', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('106', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.41/0.62  thf('107', plain,
% 0.41/0.62      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['99', '106'])).
% 0.41/0.62  thf('108', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('109', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('110', plain,
% 0.41/0.62      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.41/0.62  thf('111', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('112', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         ((v3_funct_2 @ (k2_funct_2 @ X20 @ X21) @ X20 @ X20)
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.41/0.62          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.41/0.62          | ~ (v1_funct_1 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.41/0.62  thf('113', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.62        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.41/0.62  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('115', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('116', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('117', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('118', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.41/0.62  thf('119', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['110', '118'])).
% 0.41/0.62  thf('120', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (v2_funct_2 @ X19 @ X18)
% 0.41/0.62          | ((k2_relat_1 @ X19) = (X18))
% 0.41/0.62          | ~ (v5_relat_1 @ X19 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.41/0.62  thf('121', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.41/0.62        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.41/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['119', '120'])).
% 0.41/0.62  thf('122', plain,
% 0.41/0.62      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.41/0.62  thf('123', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.62          | (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.62  thf('124', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.41/0.62        | (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['122', '123'])).
% 0.41/0.62  thf('125', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.62  thf('126', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['124', '125'])).
% 0.41/0.62  thf('127', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('128', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['126', '127'])).
% 0.41/0.62  thf('129', plain,
% 0.41/0.62      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.41/0.62  thf('130', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((v5_relat_1 @ X5 @ X7)
% 0.41/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.62  thf('131', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['129', '130'])).
% 0.41/0.62  thf('132', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.41/0.62  thf('133', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['131', '132'])).
% 0.41/0.62  thf('134', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['121', '128', '133'])).
% 0.41/0.62  thf('135', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.41/0.62          | ((X4) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.41/0.62  thf('136', plain,
% 0.41/0.62      ((((sk_A) != (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.41/0.62        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['134', '135'])).
% 0.41/0.62  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['126', '127'])).
% 0.41/0.62  thf('138', plain,
% 0.41/0.62      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['136', '137'])).
% 0.41/0.62  thf('139', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('140', plain,
% 0.41/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.62        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['138', '139'])).
% 0.41/0.62  thf('141', plain, (((k2_funct_1 @ sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['140'])).
% 0.41/0.62  thf('142', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.41/0.62  thf('143', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['141', '142'])).
% 0.41/0.62  thf('144', plain,
% 0.41/0.62      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('demod', [status(thm)], ['58', '82', '90', '143'])).
% 0.41/0.62  thf('145', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('146', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.62         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.41/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.41/0.62  thf('147', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['145', '146'])).
% 0.41/0.62  thf('148', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('149', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.41/0.62  thf('150', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.41/0.62  thf('151', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.41/0.62  thf('152', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.41/0.62  thf('153', plain,
% 0.41/0.62      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.41/0.62  thf('154', plain, ($false), inference('demod', [status(thm)], ['144', '153'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
