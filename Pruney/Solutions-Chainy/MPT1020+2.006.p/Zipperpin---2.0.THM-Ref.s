%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZtgYZbDrH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  245 (8231 expanded)
%              Number of leaves         :   36 (2512 expanded)
%              Depth                    :   22
%              Number of atoms          : 2092 (242216 expanded)
%              Number of equality atoms :  118 (1548 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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

thf('78',plain,(
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

thf('79',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('96',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X30 @ X31 ) @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('104',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X30 @ X31 ) @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('112',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','96','104','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('115',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('119',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('120',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('123',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('125',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X30 @ X31 ) @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('128',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('129',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('130',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('132',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('134',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('137',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('138',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('139',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['123','132','141'])).

thf('143',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('146',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('147',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('149',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('150',plain,(
    v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['144','147','150'])).

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

thf('152',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t197_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('161',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','36','39'])).

thf('164',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('167',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('169',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_B
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['162','170'])).

thf('172',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('174',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('175',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('178',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('182',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('183',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('185',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('186',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['180','183','186'])).

thf('188',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('189',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('191',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('193',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( sk_B
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('196',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('199',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('200',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('201',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198','199','201'])).

thf('203',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('204',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ k1_xboole_0 @ X0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['202','205'])).

thf('207',plain,(
    $false ),
    inference(demod,[status(thm)],['172','196','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZtgYZbDrH
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 322 iterations in 0.105s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.21/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(t87_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.57             ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.57             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57           ( ( r2_relset_1 @
% 0.21/0.57               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.57               ( k6_partfun1 @ A ) ) =>
% 0.21/0.57             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.57            ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.57            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57          ( ![C:$i]:
% 0.21/0.57            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.57                ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.57                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57              ( ( r2_relset_1 @
% 0.21/0.57                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.21/0.57                  ( k6_partfun1 @ A ) ) =>
% 0.21/0.57                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k2_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.21/0.57          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 0.21/0.57          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 0.21/0.57          | ~ (v1_funct_1 @ X32))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.57        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.57        (k6_partfun1 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t36_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.57           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.57               ( r2_relset_1 @
% 0.21/0.57                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.21/0.57                 ( k6_partfun1 @ A ) ) & 
% 0.21/0.57               ( v2_funct_1 @ C ) ) =>
% 0.21/0.57             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X34)
% 0.21/0.57          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.21/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.21/0.57          | ((X34) = (k2_funct_1 @ X37))
% 0.21/0.57          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.21/0.57               (k1_partfun1 @ X36 @ X35 @ X35 @ X36 @ X37 @ X34) @ 
% 0.21/0.57               (k6_partfun1 @ X36))
% 0.21/0.57          | ((X35) = (k1_xboole_0))
% 0.21/0.57          | ((X36) = (k1_xboole_0))
% 0.21/0.57          | ~ (v2_funct_1 @ X37)
% 0.21/0.57          | ((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.21/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.21/0.57          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.21/0.57          | ~ (v1_funct_1 @ X37))),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.57          | ~ (v2_funct_1 @ X0)
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.57               (k6_partfun1 @ sk_A))
% 0.21/0.57          | ((sk_C) = (k2_funct_1 @ X0))
% 0.21/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.57          | ~ (v2_funct_1 @ X0)
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.57               (k6_partfun1 @ sk_A))
% 0.21/0.57          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_C) = (k2_funct_1 @ X0))
% 0.21/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.57               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.21/0.57               (k6_partfun1 @ sk_A))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ~ (v2_funct_1 @ X0)
% 0.21/0.57          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.57        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.57        | ((sk_A) = (k1_xboole_0))
% 0.21/0.57        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.57  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.57         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.57          | (v2_funct_2 @ X22 @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (((v2_funct_2 @ sk_B @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.57  thf(d3_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (v2_funct_2 @ X29 @ X28)
% 0.21/0.57          | ((k2_relat_1 @ X29) = (X28))
% 0.21/0.57          | ~ (v5_relat_1 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_relat_1 @ X29))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.57          | (v1_relat_1 @ X3)
% 0.21/0.57          | ~ (v1_relat_1 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X12 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('39', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.21/0.57  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['23', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.57          | (v2_funct_1 @ X22)
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (((v2_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('47', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      ((((sk_A) != (sk_A))
% 0.21/0.57        | ((sk_A) = (k1_xboole_0))
% 0.21/0.57        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['17', '18', '19', '20', '41', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.57          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.21/0.57          | ((X18) != (X21)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.57  thf('55', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.21/0.57      inference('sup-', [status(thm)], ['52', '54'])).
% 0.21/0.57  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '56', '57'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.57          | (v2_funct_2 @ X22 @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (((v2_funct_2 @ sk_C @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.57  thf('62', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('64', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (v2_funct_2 @ X29 @ X28)
% 0.21/0.57          | ((k2_relat_1 @ X29) = (X28))
% 0.21/0.57          | ~ (v5_relat_1 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_relat_1 @ X29))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.21/0.57        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.57          | (v1_relat_1 @ X3)
% 0.21/0.57          | ~ (v1_relat_1 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X12 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['66', '71', '74'])).
% 0.21/0.57  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('77', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k2_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.21/0.57         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.21/0.57         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.21/0.57         ( m1_subset_1 @
% 0.21/0.57           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_funct_2 @ X30 @ X31) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.57  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('82', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('83', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_funct_2 @ X30 @ X31) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k2_funct_2 @ X30 @ X31))
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.57  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('92', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('93', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('94', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.21/0.57  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('96', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((v1_funct_2 @ (k2_funct_2 @ X30 @ X31) @ X30 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.57  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('101', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('102', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('103', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('104', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((v3_funct_2 @ (k2_funct_2 @ X30 @ X31) @ X30 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.57        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.57  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('109', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('110', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('111', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('112', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['87', '96', '104', '112'])).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.21/0.57          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 0.21/0.57          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 0.21/0.57          | ~ (v1_funct_1 @ X32))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.21/0.57            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.57  thf('117', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('118', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.21/0.57  thf('119', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.21/0.57         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['113', '120'])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.57          | (v2_funct_2 @ X22 @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((v3_funct_2 @ (k2_funct_2 @ X30 @ X31) @ X30 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['124', '125'])).
% 0.21/0.57  thf('127', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('128', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.21/0.57  thf('129', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.21/0.57         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.21/0.57  thf('132', plain,
% 0.21/0.57      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['130', '131'])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k2_funct_2 @ X30 @ X31))
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.21/0.57          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.21/0.57          | ~ (v1_funct_1 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['133', '134'])).
% 0.21/0.57  thf('136', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('137', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.21/0.57  thf('138', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.21/0.57  thf('139', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.21/0.57  thf('140', plain,
% 0.21/0.57      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.21/0.57         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.21/0.57  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['139', '140'])).
% 0.21/0.57  thf('142', plain, ((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['123', '132', '141'])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (v2_funct_2 @ X29 @ X28)
% 0.21/0.57          | ((k2_relat_1 @ X29) = (X28))
% 0.21/0.57          | ~ (v5_relat_1 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_relat_1 @ X29))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.57  thf('144', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.21/0.57        | ~ (v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.57        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['142', '143'])).
% 0.21/0.57  thf('145', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['113', '120'])).
% 0.21/0.57  thf(cc1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( v1_relat_1 @ C ) ))).
% 0.21/0.57  thf('146', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.57         ((v1_relat_1 @ X9)
% 0.21/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.57  thf('147', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['145', '146'])).
% 0.21/0.57  thf('148', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['113', '120'])).
% 0.21/0.57  thf('149', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X12 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('150', plain, ((v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['148', '149'])).
% 0.21/0.57  thf('151', plain,
% 0.21/0.57      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['144', '147', '150'])).
% 0.21/0.57  thf(t197_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( v1_relat_1 @ B ) =>
% 0.21/0.57           ( ( ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.57               ( ( k2_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.57  thf('152', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X7)
% 0.21/0.57          | ((X8) = (X7))
% 0.21/0.57          | ((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.21/0.57          | ((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t197_relat_1])).
% 0.21/0.57  thf('153', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_A) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.21/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['151', '152'])).
% 0.21/0.57  thf('154', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['145', '146'])).
% 0.21/0.57  thf('155', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_A) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['153', '154'])).
% 0.21/0.57  thf('156', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('157', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['155', '156'])).
% 0.21/0.57  thf('158', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['157'])).
% 0.21/0.57  thf('159', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['77', '158'])).
% 0.21/0.57  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.57  thf('161', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['159', '160'])).
% 0.21/0.57  thf('162', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['161'])).
% 0.21/0.57  thf('163', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '36', '39'])).
% 0.21/0.57  thf('164', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('165', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['163', '164'])).
% 0.21/0.57  thf('166', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['157'])).
% 0.21/0.57  thf('167', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['165', '166'])).
% 0.21/0.57  thf('168', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('169', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['167', '168'])).
% 0.21/0.57  thf('170', plain, (((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['169'])).
% 0.21/0.57  thf('171', plain, (((sk_B) = (sk_C))),
% 0.21/0.57      inference('sup+', [status(thm)], ['162', '170'])).
% 0.21/0.57  thf('172', plain,
% 0.21/0.57      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['58', '171'])).
% 0.21/0.57  thf('173', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('174', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.57          | (v2_funct_2 @ X22 @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.57  thf('175', plain,
% 0.21/0.57      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.21/0.57        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['173', '174'])).
% 0.21/0.57  thf('176', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.21/0.57  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('178', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.21/0.57  thf('179', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (v2_funct_2 @ X29 @ X28)
% 0.21/0.57          | ((k2_relat_1 @ X29) = (X28))
% 0.21/0.57          | ~ (v5_relat_1 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_relat_1 @ X29))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.57  thf('180', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.21/0.57        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['178', '179'])).
% 0.21/0.57  thf('181', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('182', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.57         ((v1_relat_1 @ X9)
% 0.21/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.57  thf('183', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['181', '182'])).
% 0.21/0.57  thf('184', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.57  thf('185', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X12 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('186', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['184', '185'])).
% 0.21/0.57  thf('187', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['180', '183', '186'])).
% 0.21/0.57  thf('188', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('189', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['187', '188'])).
% 0.21/0.57  thf('190', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.21/0.57          | ((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['157'])).
% 0.21/0.57  thf('191', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.57        | ((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['189', '190'])).
% 0.21/0.57  thf('192', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['181', '182'])).
% 0.21/0.57  thf('193', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['191', '192'])).
% 0.21/0.57  thf('194', plain,
% 0.21/0.57      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['193'])).
% 0.21/0.57  thf('195', plain, (((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['169'])).
% 0.21/0.57  thf('196', plain, (((sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['194', '195'])).
% 0.21/0.57  thf('197', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('198', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf('199', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '55'])).
% 0.21/0.57  thf(t113_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.57  thf('200', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i]:
% 0.21/0.57         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.57  thf('201', plain,
% 0.21/0.57      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['200'])).
% 0.21/0.57  thf('202', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['197', '198', '199', '201'])).
% 0.21/0.57  thf('203', plain,
% 0.21/0.57      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['200'])).
% 0.21/0.57  thf('204', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.57  thf('205', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.57          | (r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['203', '204'])).
% 0.21/0.57  thf('206', plain,
% 0.21/0.57      (![X0 : $i]: (r2_relset_1 @ k1_xboole_0 @ X0 @ sk_B @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['202', '205'])).
% 0.21/0.57  thf('207', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['172', '196', '206'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
