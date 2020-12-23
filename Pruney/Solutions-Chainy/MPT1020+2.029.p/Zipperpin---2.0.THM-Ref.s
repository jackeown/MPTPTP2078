%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMRst6WPPk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:05 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  214 (2673 expanded)
%              Number of leaves         :   43 ( 786 expanded)
%              Depth                    :   23
%              Number of atoms          : 1880 (68096 expanded)
%              Number of equality atoms :  126 (1015 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('36',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42
        = ( k2_funct_1 @ X45 ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42 ) @ ( k6_partfun1 @ X44 ) )
      | ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('43',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('44',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42
        = ( k2_funct_1 @ X45 ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42 ) @ ( k6_relat_1 @ X44 ) )
      | ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('63',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['68','71','74'])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['60','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','54','55','56','57','76','82'])).

thf('84',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('95',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['100','103','106'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('109',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['101','102'])).

thf('111',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['68','71','74'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('117',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('119',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('124',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('125',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('126',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['121'])).

thf('128',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['113'])).

thf('129',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['126','127','128'])).

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

thf('130',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X2 ) )
      | ( ( k5_relat_1 @ X1 @ X2 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('131',plain,
    ( ( k1_xboole_0
     != ( k6_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != ( k1_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('132',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('133',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('134',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('135',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('136',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('149',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('151',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','89'])).

thf('153',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('154',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('156',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['121'])).

thf('157',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('159',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('160',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('161',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['134','137'])).

thf('162',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['131','132','133','138','154','157','158','159','160','161'])).

thf('163',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('165',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('166',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('168',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['92','114','122','163','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yMRst6WPPk
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 680 iterations in 0.364s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.82  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.58/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.82  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.82  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.82  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.58/0.82  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.58/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.82  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.58/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.82  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.82  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.82  thf(t87_funct_2, conjecture,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.82         ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.82       ( ![C:$i]:
% 0.58/0.82         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.58/0.82             ( v3_funct_2 @ C @ A @ A ) & 
% 0.58/0.82             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.82           ( ( r2_relset_1 @
% 0.58/0.82               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.58/0.82               ( k6_partfun1 @ A ) ) =>
% 0.58/0.82             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i]:
% 0.58/0.82        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.82            ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.82            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.82          ( ![C:$i]:
% 0.58/0.82            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.58/0.82                ( v3_funct_2 @ C @ A @ A ) & 
% 0.58/0.82                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.82              ( ( r2_relset_1 @
% 0.58/0.82                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.58/0.82                  ( k6_partfun1 @ A ) ) =>
% 0.58/0.82                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k2_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.82         ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.82       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X35 : $i, X36 : $i]:
% 0.58/0.82         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 0.58/0.82          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.58/0.82          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 0.58/0.82          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 0.58/0.82          | ~ (v1_funct_1 @ X35))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.82        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.82        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.82        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.82  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.58/0.82  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '7'])).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k1_partfun1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.82         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.82         ( v1_funct_1 @ F ) & 
% 0.58/0.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.58/0.82       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.58/0.82          | ~ (v1_funct_1 @ X29)
% 0.58/0.82          | ~ (v1_funct_1 @ X32)
% 0.58/0.82          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.58/0.82          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.58/0.82              = (k5_relat_1 @ X29 @ X32)))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.58/0.82            = (k5_relat_1 @ sk_B @ X0))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.82          | ~ (v1_funct_1 @ X0)
% 0.58/0.82          | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.82  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.58/0.82            = (k5_relat_1 @ sk_B @ X0))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.82          | ~ (v1_funct_1 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.82        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['9', '14'])).
% 0.58/0.82  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.82        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.58/0.82        (k6_partfun1 @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k6_partfun1, axiom,
% 0.58/0.82    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.58/0.82  thf('19', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.82        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.58/0.82        (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.58/0.82        (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.82  thf('23', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(dt_k1_partfun1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.82         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.82         ( v1_funct_1 @ F ) & 
% 0.58/0.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.58/0.82       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.58/0.82         ( m1_subset_1 @
% 0.58/0.82           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.58/0.82           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.58/0.82  thf('25', plain,
% 0.58/0.82      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.58/0.82          | ~ (v1_funct_1 @ X21)
% 0.58/0.82          | ~ (v1_funct_1 @ X24)
% 0.58/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.58/0.82          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 0.58/0.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.58/0.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.82          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.58/0.82          | ~ (v1_funct_1 @ X1)
% 0.58/0.82          | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.82  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.58/0.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.82          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.58/0.82          | ~ (v1_funct_1 @ X1))),
% 0.58/0.82      inference('demod', [status(thm)], ['26', '27'])).
% 0.58/0.82  thf('29', plain,
% 0.58/0.82      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.82        | (m1_subset_1 @ 
% 0.58/0.82           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.58/0.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['23', '28'])).
% 0.58/0.82  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('32', plain,
% 0.58/0.82      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.58/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.58/0.82  thf(redefinition_r2_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.58/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.58/0.82          | ((X12) = (X15))
% 0.58/0.82          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ X0)
% 0.58/0.82          | ((k5_relat_1 @ sk_B @ sk_C) = (X0))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.58/0.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.58/0.82        | ((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['22', '34'])).
% 0.58/0.82  thf(dt_k6_partfun1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( m1_subset_1 @
% 0.58/0.82         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.58/0.82       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X28 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.58/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.58/0.82  thf('37', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      (![X28 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.58/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.58/0.82      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.82  thf('39', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '38'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82         = (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['17', '39'])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(t36_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82       ( ![D:$i]:
% 0.58/0.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.58/0.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.58/0.82           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.58/0.82               ( r2_relset_1 @
% 0.58/0.82                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.58/0.82                 ( k6_partfun1 @ A ) ) & 
% 0.58/0.82               ( v2_funct_1 @ C ) ) =>
% 0.58/0.82             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.82               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X42)
% 0.58/0.82          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.58/0.82          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.58/0.82          | ((X42) = (k2_funct_1 @ X45))
% 0.58/0.82          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.58/0.82               (k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42) @ 
% 0.58/0.82               (k6_partfun1 @ X44))
% 0.58/0.82          | ((X43) = (k1_xboole_0))
% 0.58/0.82          | ((X44) = (k1_xboole_0))
% 0.58/0.82          | ~ (v2_funct_1 @ X45)
% 0.58/0.82          | ((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 0.58/0.82          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.58/0.82          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.58/0.82          | ~ (v1_funct_1 @ X45))),
% 0.58/0.82      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.58/0.82  thf('43', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X42)
% 0.58/0.82          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.58/0.82          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.58/0.82          | ((X42) = (k2_funct_1 @ X45))
% 0.58/0.82          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.58/0.82               (k1_partfun1 @ X44 @ X43 @ X43 @ X44 @ X45 @ X42) @ 
% 0.58/0.82               (k6_relat_1 @ X44))
% 0.58/0.82          | ((X43) = (k1_xboole_0))
% 0.58/0.82          | ((X44) = (k1_xboole_0))
% 0.58/0.82          | ~ (v2_funct_1 @ X45)
% 0.58/0.82          | ((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 0.58/0.82          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.58/0.82          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.58/0.82          | ~ (v1_funct_1 @ X45))),
% 0.58/0.82      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.82  thf('45', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X0)
% 0.58/0.82          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.58/0.82          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.58/0.82          | ~ (v2_funct_1 @ X0)
% 0.58/0.82          | ((sk_A) = (k1_xboole_0))
% 0.58/0.82          | ((sk_A) = (k1_xboole_0))
% 0.58/0.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.58/0.82               (k6_relat_1 @ sk_A))
% 0.58/0.82          | ((sk_C) = (k2_funct_1 @ X0))
% 0.58/0.82          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.58/0.82          | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.82      inference('sup-', [status(thm)], ['41', '44'])).
% 0.58/0.82  thf('46', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X0)
% 0.58/0.82          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.58/0.82          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.58/0.82          | ~ (v2_funct_1 @ X0)
% 0.58/0.82          | ((sk_A) = (k1_xboole_0))
% 0.58/0.82          | ((sk_A) = (k1_xboole_0))
% 0.58/0.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.58/0.82               (k6_relat_1 @ sk_A))
% 0.58/0.82          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((sk_C) = (k2_funct_1 @ X0))
% 0.58/0.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.58/0.82               (k6_relat_1 @ sk_A))
% 0.58/0.82          | ((sk_A) = (k1_xboole_0))
% 0.58/0.82          | ~ (v2_funct_1 @ X0)
% 0.58/0.82          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.58/0.82          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.58/0.82          | ~ (v1_funct_1 @ X0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.58/0.82           (k6_relat_1 @ sk_A))
% 0.58/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.58/0.82        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.82        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.58/0.82        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.58/0.82        | ~ (v2_funct_1 @ sk_B)
% 0.58/0.82        | ((sk_A) = (k1_xboole_0))
% 0.58/0.82        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['40', '49'])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (![X28 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.58/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.58/0.82      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.58/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.58/0.82          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.58/0.82          | ((X12) != (X15)))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.82         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.58/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.58/0.82      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['51', '53'])).
% 0.58/0.82  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('58', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.82  thf('59', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.82         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.58/0.82          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc2_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.82         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.58/0.82  thf('62', plain,
% 0.58/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.58/0.82          | (v2_funct_2 @ X16 @ X18)
% 0.58/0.82          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.58/0.82  thf('63', plain,
% 0.58/0.82      (((v2_funct_2 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.82        | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['61', '62'])).
% 0.58/0.82  thf('64', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('66', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.58/0.82      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.58/0.82  thf(d3_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.58/0.82       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      (![X19 : $i, X20 : $i]:
% 0.58/0.82         (~ (v2_funct_2 @ X20 @ X19)
% 0.58/0.82          | ((k2_relat_1 @ X20) = (X19))
% 0.58/0.82          | ~ (v5_relat_1 @ X20 @ X19)
% 0.58/0.82          | ~ (v1_relat_1 @ X20))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.58/0.82  thf('68', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ sk_B)
% 0.58/0.82        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.58/0.82        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['66', '67'])).
% 0.58/0.82  thf('69', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( v1_relat_1 @ C ) ))).
% 0.58/0.82  thf('70', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.82         ((v1_relat_1 @ X3)
% 0.58/0.82          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.82  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.82  thf('72', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc2_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.82  thf('73', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         ((v5_relat_1 @ X6 @ X8)
% 0.58/0.82          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.82  thf('74', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.58/0.82      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.82  thf('75', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['68', '71', '74'])).
% 0.58/0.82  thf('76', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['60', '75'])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('78', plain,
% 0.58/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.58/0.82          | (v2_funct_1 @ X16)
% 0.58/0.82          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.58/0.82  thf('79', plain,
% 0.58/0.82      (((v2_funct_1 @ sk_B)
% 0.58/0.82        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.82        | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['77', '78'])).
% 0.58/0.82  thf('80', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('82', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.58/0.82  thf('83', plain,
% 0.58/0.82      ((((sk_A) != (sk_A))
% 0.58/0.82        | ((sk_A) = (k1_xboole_0))
% 0.58/0.82        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.58/0.82      inference('demod', [status(thm)],
% 0.58/0.82                ['50', '54', '55', '56', '57', '76', '82'])).
% 0.58/0.82  thf('84', plain,
% 0.58/0.82      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['83'])).
% 0.58/0.82  thf('85', plain,
% 0.58/0.82      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '7'])).
% 0.58/0.82  thf('86', plain,
% 0.58/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['84', '85'])).
% 0.58/0.82  thf('87', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('88', plain,
% 0.58/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.82         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.58/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.58/0.82      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.82  thf('89', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.58/0.82      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.82  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf('92', plain,
% 0.58/0.82      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.58/0.82      inference('demod', [status(thm)], ['8', '90', '91'])).
% 0.58/0.82  thf('93', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('94', plain,
% 0.58/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.82         (~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.58/0.82          | (v2_funct_2 @ X16 @ X18)
% 0.58/0.82          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.58/0.82  thf('95', plain,
% 0.58/0.82      (((v2_funct_2 @ sk_C @ sk_A)
% 0.58/0.82        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.58/0.82        | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.82      inference('sup-', [status(thm)], ['93', '94'])).
% 0.58/0.82  thf('96', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('98', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.58/0.82      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.82  thf('99', plain,
% 0.58/0.82      (![X19 : $i, X20 : $i]:
% 0.58/0.82         (~ (v2_funct_2 @ X20 @ X19)
% 0.58/0.82          | ((k2_relat_1 @ X20) = (X19))
% 0.58/0.82          | ~ (v5_relat_1 @ X20 @ X19)
% 0.58/0.82          | ~ (v1_relat_1 @ X20))),
% 0.58/0.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.58/0.82  thf('100', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ sk_C)
% 0.58/0.82        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.58/0.82        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['98', '99'])).
% 0.58/0.82  thf('101', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('102', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.82         ((v1_relat_1 @ X3)
% 0.58/0.82          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.82  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.82      inference('sup-', [status(thm)], ['101', '102'])).
% 0.58/0.82  thf('104', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('105', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         ((v5_relat_1 @ X6 @ X8)
% 0.58/0.82          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.82  thf('106', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.58/0.82      inference('sup-', [status(thm)], ['104', '105'])).
% 0.58/0.82  thf('107', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['100', '103', '106'])).
% 0.58/0.82  thf(t64_relat_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ A ) =>
% 0.58/0.82       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.82           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.82  thf('108', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.58/0.82          | ((X0) = (k1_xboole_0))
% 0.58/0.82          | ~ (v1_relat_1 @ X0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.58/0.82  thf('109', plain,
% 0.58/0.82      ((((sk_A) != (k1_xboole_0))
% 0.58/0.82        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.82        | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['107', '108'])).
% 0.58/0.82  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.82      inference('sup-', [status(thm)], ['101', '102'])).
% 0.58/0.82  thf('111', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['109', '110'])).
% 0.58/0.82  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf('113', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['111', '112'])).
% 0.58/0.82  thf('114', plain, (((sk_C) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['113'])).
% 0.58/0.82  thf('115', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['68', '71', '74'])).
% 0.58/0.82  thf('116', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.58/0.82          | ((X0) = (k1_xboole_0))
% 0.58/0.82          | ~ (v1_relat_1 @ X0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.58/0.82  thf('117', plain,
% 0.58/0.82      ((((sk_A) != (k1_xboole_0))
% 0.58/0.82        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['115', '116'])).
% 0.58/0.82  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.82  thf('119', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['117', '118'])).
% 0.58/0.82  thf('120', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf('121', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['119', '120'])).
% 0.58/0.82  thf('122', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['121'])).
% 0.58/0.82  thf('123', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '38'])).
% 0.58/0.82  thf('124', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.58/0.82  thf('125', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.58/0.82  thf('126', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.58/0.82  thf('127', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['121'])).
% 0.58/0.82  thf('128', plain, (((sk_C) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['113'])).
% 0.58/0.82  thf('129', plain,
% 0.58/0.82      (((k5_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.58/0.82  thf(t64_funct_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.82           ( ( ( v2_funct_1 @ A ) & 
% 0.58/0.82               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.58/0.82               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.58/0.82             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.58/0.82  thf('130', plain,
% 0.58/0.82      (![X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ X1)
% 0.58/0.82          | ~ (v1_funct_1 @ X1)
% 0.58/0.82          | ((X1) = (k2_funct_1 @ X2))
% 0.58/0.82          | ((k5_relat_1 @ X1 @ X2) != (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.58/0.82          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X2))
% 0.58/0.82          | ~ (v2_funct_1 @ X2)
% 0.58/0.82          | ~ (v1_funct_1 @ X2)
% 0.58/0.82          | ~ (v1_relat_1 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.58/0.82  thf('131', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k6_relat_1 @ (k2_relat_1 @ k1_xboole_0)))
% 0.58/0.82        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.82        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.58/0.82        | ~ (v2_funct_1 @ k1_xboole_0)
% 0.58/0.82        | ((k2_relat_1 @ k1_xboole_0) != (k1_relat_1 @ k1_xboole_0))
% 0.58/0.82        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.58/0.82        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.58/0.82        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['129', '130'])).
% 0.58/0.82  thf(t60_relat_1, axiom,
% 0.58/0.82    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.58/0.82     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.82  thf('132', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.82  thf('133', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.58/0.82  thf('134', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.58/0.82  thf('135', plain,
% 0.58/0.82      (![X28 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.58/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.58/0.82      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.82  thf('136', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.82         ((v1_relat_1 @ X3)
% 0.58/0.82          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.82  thf('137', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['135', '136'])).
% 0.58/0.82  thf('138', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.82      inference('sup+', [status(thm)], ['134', '137'])).
% 0.58/0.82  thf('139', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('140', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('141', plain,
% 0.58/0.82      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.58/0.82          | ~ (v1_funct_1 @ X21)
% 0.58/0.82          | ~ (v1_funct_1 @ X24)
% 0.58/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.58/0.82          | (v1_funct_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.58/0.82  thf('142', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.82          | ~ (v1_funct_1 @ X0)
% 0.58/0.82          | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['140', '141'])).
% 0.58/0.82  thf('143', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('144', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.58/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.82          | ~ (v1_funct_1 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['142', '143'])).
% 0.58/0.82  thf('145', plain,
% 0.58/0.82      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.82        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['139', '144'])).
% 0.58/0.82  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('147', plain,
% 0.58/0.82      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['145', '146'])).
% 0.58/0.82  thf('148', plain,
% 0.58/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.58/0.82         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('149', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['147', '148'])).
% 0.58/0.82  thf('150', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['35', '38'])).
% 0.58/0.82  thf('151', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['149', '150'])).
% 0.58/0.82  thf('152', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['86', '89'])).
% 0.58/0.82  thf('153', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.58/0.82  thf('154', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.58/0.82  thf('155', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.58/0.82  thf('156', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['121'])).
% 0.58/0.82  thf('157', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['155', '156'])).
% 0.58/0.82  thf('158', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.82  thf('159', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.82  thf('160', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.58/0.82  thf('161', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.82      inference('sup+', [status(thm)], ['134', '137'])).
% 0.58/0.82  thf('162', plain,
% 0.58/0.82      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.82        | ((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.82        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)],
% 0.58/0.82                ['131', '132', '133', '138', '154', '157', '158', '159', 
% 0.58/0.82                 '160', '161'])).
% 0.58/0.82  thf('163', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['162'])).
% 0.58/0.82  thf('164', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.58/0.82  thf('165', plain,
% 0.58/0.82      (![X28 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.58/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.58/0.82      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.82  thf('166', plain,
% 0.58/0.82      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.58/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['164', '165'])).
% 0.58/0.82  thf('167', plain,
% 0.58/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.82         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.58/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.58/0.82      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.82  thf('168', plain,
% 0.58/0.82      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['166', '167'])).
% 0.58/0.82  thf('169', plain, ($false),
% 0.58/0.82      inference('demod', [status(thm)], ['92', '114', '122', '163', '168'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
