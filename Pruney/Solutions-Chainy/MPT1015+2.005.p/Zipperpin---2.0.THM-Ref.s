%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noHE96kqtC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:47 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  256 (96059 expanded)
%              Number of leaves         :   41 (27892 expanded)
%              Depth                    :   39
%              Number of atoms          : 2585 (2272299 expanded)
%              Number of equality atoms :  198 (36945 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('18',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40 ) )
      | ( v2_funct_1 @ X44 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('38',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X45 @ X46 )
        = X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X45 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('51',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('52',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('53',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('54',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k5_relat_1 @ X7 @ X6 )
       != X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k5_relat_1 @ X7 @ X6 )
       != X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k2_funct_1 @ X0 ) )
       != ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X1 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ( ( k2_funct_1 @ X1 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
       != ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
       != ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
       != ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
       != ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','75'])).

thf('77',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('88',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X8 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) )
       != ( k2_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('93',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('95',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('100',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97','98','99'])).

thf('101',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('103',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['77','78','81','102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['28','104'])).

thf('106',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','105'])).

thf('107',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('112',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('115',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X45 @ X46 )
        = X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X45 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('124',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['119','120','121','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_C
        = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_C )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['119','120','121','124'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C
        = ( k6_partfun1 @ sk_A ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_C )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference('sup-',[status(thm)],['116','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['119','120','121','124'])).

thf('138',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137'])).

thf('139',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('141',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','141'])).

thf('143',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','142'])).

thf('144',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('149',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['147','149'])).

thf('151',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('152',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('153',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('154',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','151','152','153'])).

thf('155',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('156',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('157',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('158',plain,
    ( ( sk_C
      = ( k6_partfun1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ k1_xboole_0 )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('160',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('161',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('162',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('163',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('164',plain,
    ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('167',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40 ) )
      | ( v2_funct_1 @ X44 )
      | ( X41 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('170',plain,(
    ! [X40: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X43 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ k1_xboole_0 ) ) )
      | ( v2_funct_1 @ X44 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ k1_xboole_0 @ k1_xboole_0 @ X42 @ X44 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X40 @ k1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) )
      | ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','170'])).

thf('172',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('174',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) )
      | ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','175','176'])).

thf('178',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ( v2_funct_1 @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['164','177'])).

thf('179',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('182',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('186',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('187',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['178','179','183','187','188'])).

thf('190',plain,
    ( ( sk_C
      = ( k6_partfun1 @ k1_xboole_0 ) )
    | ( ( k6_partfun1 @ k1_xboole_0 )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','189'])).

thf('191',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('192',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['178','179','183','187','188'])).

thf('194',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','194'])).

thf('196',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('197',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('198',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['79','80'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['178','179','183','187','188'])).

thf('202',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['195','198','199','200','201'])).

thf('203',plain,
    ( ( sk_C
      = ( k6_partfun1 @ k1_xboole_0 ) )
    | ( ( k6_partfun1 @ k1_xboole_0 )
     != ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['190','202'])).

thf('204',plain,
    ( sk_C
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['154','204'])).

thf('206',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['147','149'])).

thf('207',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('208',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','150'])).

thf('209',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( sk_C
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('211',plain,
    ( sk_C
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('212',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    $false ),
    inference(demod,[status(thm)],['205','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noHE96kqtC
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.26/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.26/1.45  % Solved by: fo/fo7.sh
% 1.26/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.26/1.45  % done 1415 iterations in 1.007s
% 1.26/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.26/1.45  % SZS output start Refutation
% 1.26/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.26/1.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.26/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.26/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.26/1.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.26/1.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.26/1.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.26/1.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.26/1.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.26/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.26/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.26/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.26/1.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.26/1.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.26/1.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.26/1.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.26/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.26/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.26/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.26/1.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.26/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.26/1.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.26/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.26/1.45  thf(t76_funct_2, conjecture,
% 1.26/1.45    (![A:$i,B:$i]:
% 1.26/1.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.26/1.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.26/1.45       ( ![C:$i]:
% 1.26/1.45         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.26/1.45             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.26/1.45           ( ( ( r2_relset_1 @
% 1.26/1.45                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.26/1.45               ( v2_funct_1 @ B ) ) =>
% 1.26/1.45             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 1.26/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.26/1.45    (~( ![A:$i,B:$i]:
% 1.26/1.45        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.26/1.45            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.26/1.45          ( ![C:$i]:
% 1.26/1.45            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.26/1.45                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.26/1.45              ( ( ( r2_relset_1 @
% 1.26/1.45                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.26/1.45                  ( v2_funct_1 @ B ) ) =>
% 1.26/1.45                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 1.26/1.45    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 1.26/1.45  thf('0', plain,
% 1.26/1.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(t55_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ( v2_funct_1 @ A ) =>
% 1.26/1.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.26/1.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.26/1.45  thf('1', plain,
% 1.26/1.45      (![X10 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X10)
% 1.26/1.45          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.26/1.45          | ~ (v1_funct_1 @ X10)
% 1.26/1.45          | ~ (v1_relat_1 @ X10))),
% 1.26/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.26/1.45  thf('2', plain,
% 1.26/1.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.26/1.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('3', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('4', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(dt_k1_partfun1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.26/1.45     ( ( ( v1_funct_1 @ E ) & 
% 1.26/1.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.26/1.45         ( v1_funct_1 @ F ) & 
% 1.26/1.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.26/1.45       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.26/1.45         ( m1_subset_1 @
% 1.26/1.45           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.26/1.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.26/1.45  thf('5', plain,
% 1.26/1.45      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.26/1.45         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.26/1.45          | ~ (v1_funct_1 @ X27)
% 1.26/1.45          | ~ (v1_funct_1 @ X30)
% 1.26/1.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.26/1.45          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 1.26/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 1.26/1.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.26/1.45  thf('6', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.26/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.26/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['4', '5'])).
% 1.26/1.45  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('8', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.26/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.26/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1))),
% 1.26/1.45      inference('demod', [status(thm)], ['6', '7'])).
% 1.26/1.45  thf('9', plain,
% 1.26/1.45      ((~ (v1_funct_1 @ sk_B)
% 1.26/1.45        | (m1_subset_1 @ 
% 1.26/1.45           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.26/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.26/1.45      inference('sup-', [status(thm)], ['3', '8'])).
% 1.26/1.45  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('11', plain,
% 1.26/1.45      ((m1_subset_1 @ 
% 1.26/1.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.26/1.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('demod', [status(thm)], ['9', '10'])).
% 1.26/1.45  thf(redefinition_r2_relset_1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.26/1.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.26/1.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.26/1.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.26/1.45  thf('12', plain,
% 1.26/1.45      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.26/1.45         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.26/1.45          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.26/1.45          | ((X23) = (X26))
% 1.26/1.45          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.26/1.45  thf('13', plain,
% 1.26/1.45      (![X0 : $i]:
% 1.26/1.45         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.26/1.45             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ X0)
% 1.26/1.45          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (X0))
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.26/1.45      inference('sup-', [status(thm)], ['11', '12'])).
% 1.26/1.45  thf('14', plain,
% 1.26/1.45      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.26/1.45        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['2', '13'])).
% 1.26/1.45  thf('15', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('16', plain,
% 1.26/1.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['14', '15'])).
% 1.26/1.45  thf('17', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(t26_funct_2, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.26/1.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.26/1.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.26/1.45       ( ![E:$i]:
% 1.26/1.45         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.26/1.45             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.26/1.45           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.26/1.45             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.26/1.45               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.26/1.45  thf('18', plain,
% 1.26/1.45      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X40)
% 1.26/1.45          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.26/1.45          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.26/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 1.26/1.45          | (v2_funct_1 @ X44)
% 1.26/1.45          | ((X42) = (k1_xboole_0))
% 1.26/1.45          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 1.26/1.45          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 1.26/1.45          | ~ (v1_funct_1 @ X44))),
% 1.26/1.45      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.26/1.45  thf('19', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 1.26/1.45          | ((sk_A) = (k1_xboole_0))
% 1.26/1.45          | (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 1.26/1.45          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_B))),
% 1.26/1.45      inference('sup-', [status(thm)], ['17', '18'])).
% 1.26/1.45  thf('20', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('22', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 1.26/1.45          | ((sk_A) = (k1_xboole_0))
% 1.26/1.45          | (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B)))),
% 1.26/1.45      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.26/1.45  thf('23', plain,
% 1.26/1.45      ((~ (v2_funct_1 @ sk_B)
% 1.26/1.45        | (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_A) = (k1_xboole_0))
% 1.26/1.45        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.26/1.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['16', '22'])).
% 1.26/1.45  thf('24', plain, ((v2_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('25', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('28', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.26/1.45  thf('29', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('30', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(redefinition_k1_partfun1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.26/1.45     ( ( ( v1_funct_1 @ E ) & 
% 1.26/1.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.26/1.45         ( v1_funct_1 @ F ) & 
% 1.26/1.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.26/1.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.26/1.45  thf('31', plain,
% 1.26/1.45      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.26/1.45         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.26/1.45          | ~ (v1_funct_1 @ X33)
% 1.26/1.45          | ~ (v1_funct_1 @ X36)
% 1.26/1.45          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.26/1.45          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.26/1.45              = (k5_relat_1 @ X33 @ X36)))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.26/1.45  thf('32', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.26/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.45  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('34', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.26/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X0))),
% 1.26/1.45      inference('demod', [status(thm)], ['32', '33'])).
% 1.26/1.45  thf('35', plain,
% 1.26/1.45      ((~ (v1_funct_1 @ sk_B)
% 1.26/1.45        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.26/1.45            = (k5_relat_1 @ sk_C @ sk_B)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['29', '34'])).
% 1.26/1.45  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('37', plain,
% 1.26/1.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['14', '15'])).
% 1.26/1.45  thf('38', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.26/1.45  thf('39', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(t67_funct_2, axiom,
% 1.26/1.45    (![A:$i,B:$i]:
% 1.26/1.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.26/1.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.26/1.45       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.26/1.45  thf('40', plain,
% 1.26/1.45      (![X45 : $i, X46 : $i]:
% 1.26/1.45         (((k1_relset_1 @ X45 @ X45 @ X46) = (X45))
% 1.26/1.45          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))
% 1.26/1.45          | ~ (v1_funct_2 @ X46 @ X45 @ X45)
% 1.26/1.45          | ~ (v1_funct_1 @ X46))),
% 1.26/1.45      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.26/1.45  thf('41', plain,
% 1.26/1.45      ((~ (v1_funct_1 @ sk_B)
% 1.26/1.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.26/1.45        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['39', '40'])).
% 1.26/1.45  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('43', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('44', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(redefinition_k1_relset_1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.26/1.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.26/1.45  thf('45', plain,
% 1.26/1.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.26/1.45         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.26/1.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.26/1.45  thf('46', plain,
% 1.26/1.45      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.26/1.45      inference('sup-', [status(thm)], ['44', '45'])).
% 1.26/1.45  thf('47', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.26/1.45  thf(dt_k2_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.26/1.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.26/1.45  thf('48', plain,
% 1.26/1.45      (![X5 : $i]:
% 1.26/1.45         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 1.26/1.45          | ~ (v1_funct_1 @ X5)
% 1.26/1.45          | ~ (v1_relat_1 @ X5))),
% 1.26/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.26/1.45  thf('49', plain,
% 1.26/1.45      (![X5 : $i]:
% 1.26/1.45         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.26/1.45          | ~ (v1_funct_1 @ X5)
% 1.26/1.45          | ~ (v1_relat_1 @ X5))),
% 1.26/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.26/1.45  thf(t66_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ![B:$i]:
% 1.26/1.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.26/1.45           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 1.26/1.45             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.26/1.45               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 1.26/1.45  thf('50', plain,
% 1.26/1.45      (![X12 : $i, X13 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X12)
% 1.26/1.45          | ~ (v1_funct_1 @ X12)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X13 @ X12))
% 1.26/1.45              = (k5_relat_1 @ (k2_funct_1 @ X12) @ (k2_funct_1 @ X13)))
% 1.26/1.45          | ~ (v2_funct_1 @ X12)
% 1.26/1.45          | ~ (v2_funct_1 @ X13)
% 1.26/1.45          | ~ (v1_funct_1 @ X13)
% 1.26/1.45          | ~ (v1_relat_1 @ X13))),
% 1.26/1.45      inference('cnf', [status(esa)], [t66_funct_1])).
% 1.26/1.45  thf('51', plain,
% 1.26/1.45      (![X10 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X10)
% 1.26/1.45          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.26/1.45          | ~ (v1_funct_1 @ X10)
% 1.26/1.45          | ~ (v1_relat_1 @ X10))),
% 1.26/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.26/1.45  thf('52', plain,
% 1.26/1.45      (![X5 : $i]:
% 1.26/1.45         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 1.26/1.45          | ~ (v1_funct_1 @ X5)
% 1.26/1.45          | ~ (v1_relat_1 @ X5))),
% 1.26/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.26/1.45  thf('53', plain,
% 1.26/1.45      (![X5 : $i]:
% 1.26/1.45         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.26/1.45          | ~ (v1_funct_1 @ X5)
% 1.26/1.45          | ~ (v1_relat_1 @ X5))),
% 1.26/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.26/1.45  thf('54', plain,
% 1.26/1.45      (![X10 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X10)
% 1.26/1.45          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.26/1.45          | ~ (v1_funct_1 @ X10)
% 1.26/1.45          | ~ (v1_relat_1 @ X10))),
% 1.26/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.26/1.45  thf(t44_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ![B:$i]:
% 1.26/1.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.26/1.45           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.26/1.45               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 1.26/1.45             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 1.26/1.45  thf('55', plain,
% 1.26/1.45      (![X6 : $i, X7 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X6)
% 1.26/1.45          | ~ (v1_funct_1 @ X6)
% 1.26/1.45          | ((X6) = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 1.26/1.45          | ((k5_relat_1 @ X7 @ X6) != (X7))
% 1.26/1.45          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 1.26/1.45          | ~ (v1_funct_1 @ X7)
% 1.26/1.45          | ~ (v1_relat_1 @ X7))),
% 1.26/1.45      inference('cnf', [status(esa)], [t44_funct_1])).
% 1.26/1.45  thf(redefinition_k6_partfun1, axiom,
% 1.26/1.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.26/1.45  thf('56', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.26/1.45  thf('57', plain,
% 1.26/1.45      (![X6 : $i, X7 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X6)
% 1.26/1.45          | ~ (v1_funct_1 @ X6)
% 1.26/1.45          | ((X6) = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 1.26/1.45          | ((k5_relat_1 @ X7 @ X6) != (X7))
% 1.26/1.45          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 1.26/1.45          | ~ (v1_funct_1 @ X7)
% 1.26/1.45          | ~ (v1_relat_1 @ X7))),
% 1.26/1.45      inference('demod', [status(thm)], ['55', '56'])).
% 1.26/1.45  thf('58', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1))),
% 1.26/1.45      inference('sup-', [status(thm)], ['54', '57'])).
% 1.26/1.45  thf('59', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['53', '58'])).
% 1.26/1.45  thf('60', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['59'])).
% 1.26/1.45  thf('61', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['52', '60'])).
% 1.26/1.45  thf('62', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['61'])).
% 1.26/1.45  thf('63', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ (k2_funct_1 @ X0))
% 1.26/1.45              != (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v2_funct_1 @ X1))),
% 1.26/1.45      inference('sup-', [status(thm)], ['51', '62'])).
% 1.26/1.45  thf('64', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0)) != (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ X1)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X1))))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ((k1_relat_1 @ X0) != (k2_relat_1 @ X1)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['50', '63'])).
% 1.26/1.45  thf('65', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (k2_relat_1 @ X1))
% 1.26/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X1))
% 1.26/1.45          | ((k2_funct_1 @ X1)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X1))))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X1 @ X0)) != (k2_funct_1 @ X0)))),
% 1.26/1.45      inference('simplify', [status(thm)], ['64'])).
% 1.26/1.45  thf('66', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ X1)) != (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['49', '65'])).
% 1.26/1.45  thf('67', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.26/1.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ X1)) != (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['66'])).
% 1.26/1.45  thf('68', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ X1)) != (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.26/1.45          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['48', '67'])).
% 1.26/1.45  thf('69', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X1)
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ X1)) != (k2_funct_1 @ X1))
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['68'])).
% 1.26/1.45  thf('70', plain,
% 1.26/1.45      (![X0 : $i]:
% 1.26/1.45         (((sk_A) != (k2_relat_1 @ X0))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ~ (v2_funct_1 @ sk_B)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_B)
% 1.26/1.45          | ~ (v1_relat_1 @ sk_B)
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.26/1.45      inference('sup-', [status(thm)], ['47', '69'])).
% 1.26/1.45  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('73', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(cc1_relset_1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.26/1.45       ( v1_relat_1 @ C ) ))).
% 1.26/1.45  thf('74', plain,
% 1.26/1.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.26/1.45         ((v1_relat_1 @ X14)
% 1.26/1.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.26/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.26/1.45  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.45      inference('sup-', [status(thm)], ['73', '74'])).
% 1.26/1.45  thf('76', plain,
% 1.26/1.45      (![X0 : $i]:
% 1.26/1.45         (((sk_A) != (k2_relat_1 @ X0))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k2_funct_1 @ X0)
% 1.26/1.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.26/1.45      inference('demod', [status(thm)], ['70', '71', '72', '75'])).
% 1.26/1.45  thf('77', plain,
% 1.26/1.45      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 1.26/1.45        | ((k2_funct_1 @ sk_C)
% 1.26/1.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45        | ((sk_A) != (k2_relat_1 @ sk_C)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['38', '76'])).
% 1.26/1.45  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('79', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('80', plain,
% 1.26/1.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.26/1.45         ((v1_relat_1 @ X14)
% 1.26/1.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.26/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.26/1.45  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('82', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(cc2_relset_1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.26/1.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.26/1.45  thf('83', plain,
% 1.26/1.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.26/1.45         ((v5_relat_1 @ X17 @ X19)
% 1.26/1.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.26/1.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.26/1.45  thf('84', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 1.26/1.45      inference('sup-', [status(thm)], ['82', '83'])).
% 1.26/1.45  thf(d19_relat_1, axiom,
% 1.26/1.45    (![A:$i,B:$i]:
% 1.26/1.45     ( ( v1_relat_1 @ B ) =>
% 1.26/1.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.26/1.45  thf('85', plain,
% 1.26/1.45      (![X3 : $i, X4 : $i]:
% 1.26/1.45         (~ (v5_relat_1 @ X3 @ X4)
% 1.26/1.45          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.26/1.45          | ~ (v1_relat_1 @ X3))),
% 1.26/1.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.26/1.45  thf('86', plain,
% 1.26/1.45      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 1.26/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.26/1.45  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('88', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 1.26/1.45      inference('demod', [status(thm)], ['86', '87'])).
% 1.26/1.45  thf(d10_xboole_0, axiom,
% 1.26/1.45    (![A:$i,B:$i]:
% 1.26/1.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.26/1.45  thf('89', plain,
% 1.26/1.45      (![X0 : $i, X2 : $i]:
% 1.26/1.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.26/1.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.26/1.45  thf('90', plain,
% 1.26/1.45      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))
% 1.26/1.45        | ((sk_A) = (k2_relat_1 @ sk_C)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['88', '89'])).
% 1.26/1.45  thf('91', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.26/1.45  thf(t51_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ![B:$i]:
% 1.26/1.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.26/1.45           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 1.26/1.45               ( v2_funct_1 @ A ) ) =>
% 1.26/1.45             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.26/1.45  thf('92', plain,
% 1.26/1.45      (![X8 : $i, X9 : $i]:
% 1.26/1.45         (~ (v1_relat_1 @ X8)
% 1.26/1.45          | ~ (v1_funct_1 @ X8)
% 1.26/1.45          | (r1_tarski @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X8))
% 1.26/1.45          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ X9)) != (k2_relat_1 @ X9))
% 1.26/1.45          | ~ (v2_funct_1 @ X9)
% 1.26/1.45          | ~ (v1_funct_1 @ X9)
% 1.26/1.45          | ~ (v1_relat_1 @ X9))),
% 1.26/1.45      inference('cnf', [status(esa)], [t51_funct_1])).
% 1.26/1.45  thf('93', plain,
% 1.26/1.45      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 1.26/1.45        | ~ (v1_relat_1 @ sk_B)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_B)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_B)
% 1.26/1.45        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['91', '92'])).
% 1.26/1.45  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.45      inference('sup-', [status(thm)], ['73', '74'])).
% 1.26/1.45  thf('95', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('96', plain, ((v2_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('97', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.26/1.45  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('100', plain,
% 1.26/1.45      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 1.26/1.45        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_C)))),
% 1.26/1.45      inference('demod', [status(thm)],
% 1.26/1.45                ['93', '94', '95', '96', '97', '98', '99'])).
% 1.26/1.45  thf('101', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('simplify', [status(thm)], ['100'])).
% 1.26/1.45  thf('102', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['90', '101'])).
% 1.26/1.45  thf('103', plain,
% 1.26/1.45      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 1.26/1.45        | ((k2_funct_1 @ sk_C)
% 1.26/1.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_A) != (sk_A)))),
% 1.26/1.45      inference('demod', [status(thm)], ['77', '78', '81', '102'])).
% 1.26/1.45  thf('104', plain,
% 1.26/1.45      ((~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k2_funct_1 @ sk_C)
% 1.26/1.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.26/1.45      inference('simplify', [status(thm)], ['103'])).
% 1.26/1.45  thf('105', plain,
% 1.26/1.45      ((((sk_A) = (k1_xboole_0))
% 1.26/1.45        | ((k2_funct_1 @ sk_C)
% 1.26/1.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.26/1.45      inference('sup-', [status(thm)], ['28', '104'])).
% 1.26/1.45  thf('106', plain,
% 1.26/1.45      ((((k2_funct_1 @ sk_C) = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['1', '105'])).
% 1.26/1.45  thf('107', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['90', '101'])).
% 1.26/1.45  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('110', plain,
% 1.26/1.45      ((((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 1.26/1.45  thf('111', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.26/1.45  thf('112', plain,
% 1.26/1.45      ((((sk_A) = (k1_xboole_0)) | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A)))),
% 1.26/1.45      inference('clc', [status(thm)], ['110', '111'])).
% 1.26/1.45  thf('113', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.26/1.45  thf(t61_funct_1, axiom,
% 1.26/1.45    (![A:$i]:
% 1.26/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.26/1.45       ( ( v2_funct_1 @ A ) =>
% 1.26/1.45         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.26/1.45             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.26/1.45           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.26/1.45             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.26/1.45  thf('114', plain,
% 1.26/1.45      (![X11 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X11)
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 1.26/1.45              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.26/1.45          | ~ (v1_funct_1 @ X11)
% 1.26/1.45          | ~ (v1_relat_1 @ X11))),
% 1.26/1.45      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.26/1.45  thf('115', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.26/1.45  thf('116', plain,
% 1.26/1.45      (![X11 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X11)
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 1.26/1.45              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 1.26/1.45          | ~ (v1_funct_1 @ X11)
% 1.26/1.45          | ~ (v1_relat_1 @ X11))),
% 1.26/1.45      inference('demod', [status(thm)], ['114', '115'])).
% 1.26/1.45  thf('117', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('118', plain,
% 1.26/1.45      (![X45 : $i, X46 : $i]:
% 1.26/1.45         (((k1_relset_1 @ X45 @ X45 @ X46) = (X45))
% 1.26/1.45          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))
% 1.26/1.45          | ~ (v1_funct_2 @ X46 @ X45 @ X45)
% 1.26/1.45          | ~ (v1_funct_1 @ X46))),
% 1.26/1.45      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.26/1.45  thf('119', plain,
% 1.26/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.26/1.45        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['117', '118'])).
% 1.26/1.45  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('122', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('123', plain,
% 1.26/1.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.26/1.45         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.26/1.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.26/1.45  thf('124', plain,
% 1.26/1.45      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['122', '123'])).
% 1.26/1.45  thf('125', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['119', '120', '121', '124'])).
% 1.26/1.45  thf('126', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.26/1.45          | ~ (v2_funct_1 @ X0)
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.26/1.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.26/1.45          | ~ (v1_funct_1 @ X1)
% 1.26/1.45          | ~ (v1_relat_1 @ X1)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ X0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['61'])).
% 1.26/1.45  thf('127', plain,
% 1.26/1.45      (![X0 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (sk_A))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45          | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ sk_C) != (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v2_funct_1 @ X0))),
% 1.26/1.45      inference('sup-', [status(thm)], ['125', '126'])).
% 1.26/1.45  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('130', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['119', '120', '121', '124'])).
% 1.26/1.45  thf('131', plain,
% 1.26/1.45      (![X0 : $i]:
% 1.26/1.45         (((k1_relat_1 @ X0) != (sk_A))
% 1.26/1.45          | ~ (v1_relat_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_1 @ X0)
% 1.26/1.45          | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ sk_C) != (k2_funct_1 @ X0))
% 1.26/1.45          | ~ (v2_funct_1 @ X0))),
% 1.26/1.45      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 1.26/1.45  thf('132', plain,
% 1.26/1.45      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45        | ((k1_relat_1 @ sk_C) != (sk_A)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['116', '131'])).
% 1.26/1.45  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('137', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['119', '120', '121', '124'])).
% 1.26/1.45  thf('138', plain,
% 1.26/1.45      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ((sk_A) != (sk_A)))),
% 1.26/1.45      inference('demod', [status(thm)],
% 1.26/1.45                ['132', '133', '134', '135', '136', '137'])).
% 1.26/1.45  thf('139', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C)))),
% 1.26/1.45      inference('simplify', [status(thm)], ['138'])).
% 1.26/1.45  thf('140', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['90', '101'])).
% 1.26/1.45  thf('141', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 1.26/1.45      inference('demod', [status(thm)], ['139', '140'])).
% 1.26/1.45  thf('142', plain,
% 1.26/1.45      ((((sk_A) = (k1_xboole_0))
% 1.26/1.45        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C))
% 1.26/1.45        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['113', '141'])).
% 1.26/1.45  thf('143', plain,
% 1.26/1.45      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.26/1.45        | ((sk_A) = (k1_xboole_0))
% 1.26/1.45        | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['112', '142'])).
% 1.26/1.45  thf('144', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('simplify', [status(thm)], ['143'])).
% 1.26/1.45  thf('145', plain,
% 1.26/1.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('146', plain,
% 1.26/1.45      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.26/1.45      inference('sup-', [status(thm)], ['144', '145'])).
% 1.26/1.45  thf('147', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('148', plain,
% 1.26/1.45      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.26/1.45         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.26/1.45          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.26/1.45          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 1.26/1.45          | ((X23) != (X26)))),
% 1.26/1.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.26/1.45  thf('149', plain,
% 1.26/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.26/1.45         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 1.26/1.45          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.26/1.45      inference('simplify', [status(thm)], ['148'])).
% 1.26/1.45  thf('150', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['147', '149'])).
% 1.26/1.45  thf('151', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('152', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('153', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('154', plain,
% 1.26/1.45      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.26/1.45          (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['0', '151', '152', '153'])).
% 1.26/1.45  thf('155', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 1.26/1.45      inference('demod', [status(thm)], ['139', '140'])).
% 1.26/1.45  thf('156', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('157', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('158', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ k1_xboole_0))
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k6_partfun1 @ k1_xboole_0) != (k2_funct_1 @ sk_C)))),
% 1.26/1.45      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.26/1.45  thf('159', plain,
% 1.26/1.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['14', '15'])).
% 1.26/1.45  thf('160', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('161', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('162', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('163', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('164', plain,
% 1.26/1.45      (((k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 1.26/1.45         sk_C @ sk_B) = (sk_B))),
% 1.26/1.45      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 1.26/1.45  thf('165', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('166', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('167', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('168', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_C @ 
% 1.26/1.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['165', '166', '167'])).
% 1.26/1.45  thf('169', plain,
% 1.26/1.45      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X40)
% 1.26/1.45          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.26/1.45          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.26/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 1.26/1.45          | (v2_funct_1 @ X44)
% 1.26/1.45          | ((X41) != (k1_xboole_0))
% 1.26/1.45          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 1.26/1.45          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 1.26/1.45          | ~ (v1_funct_1 @ X44))),
% 1.26/1.45      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.26/1.45  thf('170', plain,
% 1.26/1.45      (![X40 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X44)
% 1.26/1.45          | ~ (v1_funct_2 @ X44 @ X43 @ k1_xboole_0)
% 1.26/1.45          | ~ (m1_subset_1 @ X44 @ 
% 1.26/1.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ k1_xboole_0)))
% 1.26/1.45          | (v2_funct_1 @ X44)
% 1.26/1.45          | ~ (v2_funct_1 @ 
% 1.26/1.45               (k1_partfun1 @ X43 @ k1_xboole_0 @ k1_xboole_0 @ X42 @ X44 @ X40))
% 1.26/1.45          | ~ (m1_subset_1 @ X40 @ 
% 1.26/1.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X42)))
% 1.26/1.45          | ~ (v1_funct_2 @ X40 @ k1_xboole_0 @ X42)
% 1.26/1.45          | ~ (v1_funct_1 @ X40))),
% 1.26/1.45      inference('simplify', [status(thm)], ['169'])).
% 1.26/1.45  thf('171', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ X1)
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ 
% 1.26/1.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)))
% 1.26/1.45          | ~ (v2_funct_1 @ 
% 1.26/1.45               (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ 
% 1.26/1.45                sk_C @ X0))
% 1.26/1.45          | (v2_funct_1 @ sk_C)
% 1.26/1.45          | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)
% 1.26/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.26/1.45      inference('sup-', [status(thm)], ['168', '170'])).
% 1.26/1.45  thf('172', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('173', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('174', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('175', plain, ((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)),
% 1.26/1.45      inference('demod', [status(thm)], ['172', '173', '174'])).
% 1.26/1.45  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('177', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         (~ (v1_funct_1 @ X0)
% 1.26/1.45          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ X1)
% 1.26/1.45          | ~ (m1_subset_1 @ X0 @ 
% 1.26/1.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)))
% 1.26/1.45          | ~ (v2_funct_1 @ 
% 1.26/1.45               (k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ 
% 1.26/1.45                sk_C @ X0))
% 1.26/1.45          | (v2_funct_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['171', '175', '176'])).
% 1.26/1.45  thf('178', plain,
% 1.26/1.45      ((~ (v2_funct_1 @ sk_B)
% 1.26/1.45        | (v2_funct_1 @ sk_C)
% 1.26/1.45        | ~ (m1_subset_1 @ sk_B @ 
% 1.26/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 1.26/1.45        | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_B))),
% 1.26/1.45      inference('sup-', [status(thm)], ['164', '177'])).
% 1.26/1.45  thf('179', plain, ((v2_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('180', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('181', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('182', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('183', plain,
% 1.26/1.45      ((m1_subset_1 @ sk_B @ 
% 1.26/1.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.26/1.45  thf('184', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('185', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('186', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('187', plain, ((v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 1.26/1.45      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.26/1.45  thf('188', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 1.26/1.45      inference('demod', [status(thm)], ['178', '179', '183', '187', '188'])).
% 1.26/1.45  thf('190', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ k1_xboole_0))
% 1.26/1.45        | ((k6_partfun1 @ k1_xboole_0) != (k2_funct_1 @ sk_C)))),
% 1.26/1.45      inference('demod', [status(thm)], ['158', '189'])).
% 1.26/1.45  thf('191', plain,
% 1.26/1.45      (![X10 : $i]:
% 1.26/1.45         (~ (v2_funct_1 @ X10)
% 1.26/1.45          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.26/1.45          | ~ (v1_funct_1 @ X10)
% 1.26/1.45          | ~ (v1_relat_1 @ X10))),
% 1.26/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.26/1.45  thf('192', plain,
% 1.26/1.45      ((~ (v2_funct_1 @ sk_C)
% 1.26/1.45        | ((k2_funct_1 @ sk_C)
% 1.26/1.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.26/1.45      inference('simplify', [status(thm)], ['103'])).
% 1.26/1.45  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 1.26/1.45      inference('demod', [status(thm)], ['178', '179', '183', '187', '188'])).
% 1.26/1.45  thf('194', plain,
% 1.26/1.45      (((k2_funct_1 @ sk_C)
% 1.26/1.45         = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.26/1.45      inference('demod', [status(thm)], ['192', '193'])).
% 1.26/1.45  thf('195', plain,
% 1.26/1.45      ((((k2_funct_1 @ sk_C) = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.26/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.26/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.26/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.26/1.45      inference('sup+', [status(thm)], ['191', '194'])).
% 1.26/1.45  thf('196', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['90', '101'])).
% 1.26/1.45  thf('197', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('198', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_C))),
% 1.26/1.45      inference('demod', [status(thm)], ['196', '197'])).
% 1.26/1.45  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.45  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 1.26/1.45      inference('demod', [status(thm)], ['178', '179', '183', '187', '188'])).
% 1.26/1.45  thf('202', plain, (((k2_funct_1 @ sk_C) = (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['195', '198', '199', '200', '201'])).
% 1.26/1.45  thf('203', plain,
% 1.26/1.45      ((((sk_C) = (k6_partfun1 @ k1_xboole_0))
% 1.26/1.45        | ((k6_partfun1 @ k1_xboole_0) != (k6_partfun1 @ k1_xboole_0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['190', '202'])).
% 1.26/1.45  thf('204', plain, (((sk_C) = (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['203'])).
% 1.26/1.45  thf('205', plain,
% 1.26/1.45      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 1.26/1.45          (k6_partfun1 @ k1_xboole_0) @ (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['154', '204'])).
% 1.26/1.45  thf('206', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.26/1.45      inference('sup-', [status(thm)], ['147', '149'])).
% 1.26/1.45  thf('207', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('208', plain, (((sk_A) = (k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['146', '150'])).
% 1.26/1.45  thf('209', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_C)),
% 1.26/1.45      inference('demod', [status(thm)], ['206', '207', '208'])).
% 1.26/1.45  thf('210', plain, (((sk_C) = (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['203'])).
% 1.26/1.45  thf('211', plain, (((sk_C) = (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('simplify', [status(thm)], ['203'])).
% 1.26/1.45  thf('212', plain,
% 1.26/1.45      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 1.26/1.45        (k6_partfun1 @ k1_xboole_0) @ (k6_partfun1 @ k1_xboole_0))),
% 1.26/1.45      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.26/1.45  thf('213', plain, ($false), inference('demod', [status(thm)], ['205', '212'])).
% 1.26/1.45  
% 1.26/1.45  % SZS output end Refutation
% 1.26/1.45  
% 1.26/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
