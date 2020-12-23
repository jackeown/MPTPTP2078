%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imwlAqNSOc

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:46 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 499 expanded)
%              Number of leaves         :   40 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          : 1353 (11423 expanded)
%              Number of equality atoms :   98 ( 346 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t75_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
              & ( ( k2_relset_1 @ A @ A @ B )
                = A ) )
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
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
                & ( ( k2_relset_1 @ A @ A @ B )
                  = A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( X35 = X38 )
      | ~ ( r2_relset_1 @ X36 @ X37 @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31','32','37','38','41'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('47',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('61',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','67','68','69','70','71'])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ ( k2_zfmisc_1 @ X17 @ ( k2_relat_1 @ X16 ) ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_C @ X0 )
        = ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['52','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['47','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('80',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('81',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_partfun1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('85',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_partfun1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf(t156_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( A
                    = ( k2_relat_1 @ B ) )
                  & ( ( k1_relat_1 @ C )
                    = A )
                  & ( ( k1_relat_1 @ D )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k5_relat_1 @ B @ D ) ) )
               => ( C = D ) ) ) ) ) )).

thf('86',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X22
       != ( k2_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X20 )
       != X22 )
      | ( ( k1_relat_1 @ X23 )
       != X22 )
      | ( ( k5_relat_1 @ X21 @ X20 )
       != ( k5_relat_1 @ X21 @ X23 ) )
      | ( X20 = X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t156_funct_1])).

thf('87',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X20 = X23 )
      | ( ( k5_relat_1 @ X21 @ X20 )
       != ( k5_relat_1 @ X21 @ X23 ) )
      | ( ( k1_relat_1 @ X23 )
       != ( k2_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k2_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
       != ( k2_relat_1 @ sk_B ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_B ) )
      | ( ( k6_partfun1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('89',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('90',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('95',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','36'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k5_relat_1 @ sk_B @ X0 ) )
      | ( sk_A != sk_A )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ( ( k6_partfun1 @ sk_A )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','91','94','97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_partfun1 @ sk_A )
        = X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ( sk_B
       != ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( sk_A != sk_A )
    | ( sk_B
     != ( k5_relat_1 @ sk_B @ sk_C ) )
    | ( ( k6_partfun1 @ sk_A )
      = sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('108',plain,
    ( ( sk_A != sk_A )
    | ( sk_B != sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( k6_partfun1 @ sk_A )
    = sk_C ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( r2_relset_1 @ X36 @ X37 @ X35 @ X38 )
      | ( X35 != X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('112',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_relset_1 @ X36 @ X37 @ X38 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imwlAqNSOc
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 363 iterations in 0.219s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(t75_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.47/0.67             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.67           ( ( ( r2_relset_1 @
% 0.47/0.67                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.47/0.67               ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.47/0.67             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.67            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.67          ( ![C:$i]:
% 0.47/0.67            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.47/0.67                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.67              ( ( ( r2_relset_1 @
% 0.47/0.67                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.47/0.67                  ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.47/0.67                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t75_funct_2])).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.67        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_partfun1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.67         ( v1_funct_1 @ F ) & 
% 0.47/0.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.67       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.47/0.67          | ~ (v1_funct_1 @ X45)
% 0.47/0.67          | ~ (v1_funct_1 @ X48)
% 0.47/0.67          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.47/0.67          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 0.47/0.67              = (k5_relat_1 @ X45 @ X48)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.47/0.67            = (k5_relat_1 @ sk_B @ X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.47/0.67            = (k5_relat_1 @ sk_B @ X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.67          | ~ (v1_funct_1 @ X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.47/0.67            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['2', '7'])).
% 0.47/0.67  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.47/0.67         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ sk_B)),
% 0.47/0.67      inference('demod', [status(thm)], ['1', '10'])).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(dt_k1_partfun1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.67         ( v1_funct_1 @ F ) & 
% 0.47/0.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.67       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.47/0.67         ( m1_subset_1 @
% 0.47/0.67           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.47/0.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.47/0.67          | ~ (v1_funct_1 @ X39)
% 0.47/0.67          | ~ (v1_funct_1 @ X42)
% 0.47/0.67          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.47/0.67          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 0.47/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.47/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.67  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.47/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.47/0.67          | ~ (v1_funct_1 @ X1))),
% 0.47/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | (m1_subset_1 @ 
% 0.47/0.67           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.47/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['12', '17'])).
% 0.47/0.67  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.47/0.67         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.47/0.67  thf(redefinition_r2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.47/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.47/0.67          | ((X35) = (X38))
% 0.47/0.67          | ~ (r2_relset_1 @ X36 @ X37 @ X35 @ X38))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ X0)
% 0.47/0.67          | ((k5_relat_1 @ sk_B @ sk_C) = (X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.47/0.67        | ((k5_relat_1 @ sk_B @ sk_C) = (sk_B)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['11', '23'])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('26', plain, (((k5_relat_1 @ sk_B @ sk_C) = (sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.67  thf(t27_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.47/0.67             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X24 : $i, X25 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X24)
% 0.47/0.67          | ~ (v1_funct_1 @ X24)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X24) @ (k1_relat_1 @ X25))
% 0.47/0.67          | ((k1_relat_1 @ (k5_relat_1 @ X24 @ X25)) != (k1_relat_1 @ X24))
% 0.47/0.67          | ~ (v1_funct_1 @ X25)
% 0.47/0.67          | ~ (v1_relat_1 @ X25))),
% 0.47/0.67      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | (r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( v1_relat_1 @ C ) ))).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.67         ((v1_relat_1 @ X26)
% 0.47/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.67  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.47/0.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.67  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('37', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.67         ((v1_relat_1 @ X26)
% 0.47/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.67  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.47/0.67        | (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '31', '32', '37', '38', '41'])).
% 0.47/0.67  thf('43', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.47/0.67      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.67  thf(t91_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.67         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.47/0.67          | ((k1_relat_1 @ (k7_relat_1 @ X15 @ X14)) = (X14))
% 0.47/0.67          | ~ (v1_relat_1 @ X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.67  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('47', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t3_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.67  thf('50', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf(t28_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i]:
% 0.47/0.67         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      (((k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A)) = (sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.67  thf('53', plain, (((k5_relat_1 @ sk_B @ sk_C) = (sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.67  thf(t45_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( v1_relat_1 @ B ) =>
% 0.47/0.67           ( r1_tarski @
% 0.47/0.67             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (![X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X9)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.47/0.67             (k2_relat_1 @ X9))
% 0.47/0.67          | ~ (v1_relat_1 @ X10))),
% 0.47/0.67      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('55', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.47/0.67               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.47/0.67          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_relat_1 @ sk_B))
% 0.47/0.67        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_B @ sk_C)))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['53', '56'])).
% 0.47/0.67  thf('58', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(dt_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k2_relset_1 @ X29 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))
% 0.47/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('63', plain,
% 0.47/0.67      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.47/0.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['61', '64'])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.67  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.47/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.67  thf('68', plain, (((k5_relat_1 @ sk_B @ sk_C) = (sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.67  thf('69', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('72', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.67      inference('demod', [status(thm)],
% 0.47/0.67                ['57', '58', '67', '68', '69', '70', '71'])).
% 0.47/0.67  thf(t96_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( k7_relat_1 @ B @ A ) =
% 0.47/0.67         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.67  thf('73', plain,
% 0.47/0.67      (![X16 : $i, X17 : $i]:
% 0.47/0.67         (((k7_relat_1 @ X16 @ X17)
% 0.47/0.67            = (k3_xboole_0 @ X16 @ (k2_zfmisc_1 @ X17 @ (k2_relat_1 @ X16))))
% 0.47/0.67          | ~ (v1_relat_1 @ X16))),
% 0.47/0.67      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k7_relat_1 @ sk_C @ X0)
% 0.47/0.67            = (k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.47/0.67          | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup+', [status(thm)], ['72', '73'])).
% 0.47/0.67  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k7_relat_1 @ sk_C @ X0)
% 0.47/0.67           = (k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('77', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['52', '76'])).
% 0.47/0.67  thf('78', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['47', '77'])).
% 0.47/0.67  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf(t80_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.47/0.67  thf('80', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         (((k5_relat_1 @ X13 @ (k6_relat_1 @ (k2_relat_1 @ X13))) = (X13))
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.47/0.67  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.67    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.67  thf('81', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.67  thf('82', plain,
% 0.47/0.67      (![X13 : $i]:
% 0.47/0.67         (((k5_relat_1 @ X13 @ (k6_partfun1 @ (k2_relat_1 @ X13))) = (X13))
% 0.47/0.67          | ~ (v1_relat_1 @ X13))),
% 0.47/0.67      inference('demod', [status(thm)], ['80', '81'])).
% 0.47/0.67  thf('83', plain,
% 0.47/0.67      ((((k5_relat_1 @ sk_B @ (k6_partfun1 @ sk_A)) = (sk_B))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['79', '82'])).
% 0.47/0.67  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('85', plain, (((k5_relat_1 @ sk_B @ (k6_partfun1 @ sk_A)) = (sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['83', '84'])).
% 0.47/0.67  thf(t156_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.67           ( ![D:$i]:
% 0.47/0.67             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.47/0.67               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.47/0.67                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.47/0.67                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.47/0.67                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.47/0.67                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 0.47/0.67  thf('86', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X20)
% 0.47/0.67          | ~ (v1_funct_1 @ X20)
% 0.47/0.67          | ((X22) != (k2_relat_1 @ X21))
% 0.47/0.67          | ((k1_relat_1 @ X20) != (X22))
% 0.47/0.67          | ((k1_relat_1 @ X23) != (X22))
% 0.47/0.67          | ((k5_relat_1 @ X21 @ X20) != (k5_relat_1 @ X21 @ X23))
% 0.47/0.67          | ((X20) = (X23))
% 0.47/0.67          | ~ (v1_funct_1 @ X23)
% 0.47/0.67          | ~ (v1_relat_1 @ X23)
% 0.47/0.67          | ~ (v1_funct_1 @ X21)
% 0.47/0.67          | ~ (v1_relat_1 @ X21))),
% 0.47/0.67      inference('cnf', [status(esa)], [t156_funct_1])).
% 0.47/0.67  thf('87', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X21)
% 0.47/0.67          | ~ (v1_funct_1 @ X21)
% 0.47/0.67          | ~ (v1_relat_1 @ X23)
% 0.47/0.67          | ~ (v1_funct_1 @ X23)
% 0.47/0.67          | ((X20) = (X23))
% 0.47/0.67          | ((k5_relat_1 @ X21 @ X20) != (k5_relat_1 @ X21 @ X23))
% 0.47/0.67          | ((k1_relat_1 @ X23) != (k2_relat_1 @ X21))
% 0.47/0.67          | ((k1_relat_1 @ X20) != (k2_relat_1 @ X21))
% 0.47/0.67          | ~ (v1_funct_1 @ X20)
% 0.47/0.67          | ~ (v1_relat_1 @ X20))),
% 0.47/0.67      inference('simplify', [status(thm)], ['86'])).
% 0.47/0.67  thf('88', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((sk_B) != (k5_relat_1 @ sk_B @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.47/0.67          | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.47/0.67          | ((k1_relat_1 @ (k6_partfun1 @ sk_A)) != (k2_relat_1 @ sk_B))
% 0.47/0.67          | ((k1_relat_1 @ X0) != (k2_relat_1 @ sk_B))
% 0.47/0.67          | ((k6_partfun1 @ sk_A) = (X0))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ sk_B)
% 0.47/0.67          | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['85', '87'])).
% 0.47/0.67  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.47/0.67  thf('89', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.47/0.67  thf('90', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.67  thf('91', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.47/0.67      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.67  thf(fc3_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.67  thf('92', plain, (![X19 : $i]: (v1_funct_1 @ (k6_relat_1 @ X19))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.67  thf('93', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.67  thf('94', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 0.47/0.67      inference('demod', [status(thm)], ['92', '93'])).
% 0.47/0.67  thf(t71_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.67       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.67  thf('95', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.67  thf('96', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.67  thf('97', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 0.47/0.67      inference('demod', [status(thm)], ['95', '96'])).
% 0.47/0.67  thf('98', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('99', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('101', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('102', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((sk_B) != (k5_relat_1 @ sk_B @ X0))
% 0.47/0.67          | ((sk_A) != (sk_A))
% 0.47/0.67          | ((k1_relat_1 @ X0) != (sk_A))
% 0.47/0.67          | ((k6_partfun1 @ sk_A) = (X0))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('demod', [status(thm)],
% 0.47/0.67                ['88', '91', '94', '97', '98', '99', '100', '101'])).
% 0.47/0.67  thf('103', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ((k6_partfun1 @ sk_A) = (X0))
% 0.47/0.67          | ((k1_relat_1 @ X0) != (sk_A))
% 0.47/0.67          | ((sk_B) != (k5_relat_1 @ sk_B @ X0)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['102'])).
% 0.47/0.67  thf('104', plain,
% 0.47/0.67      ((((sk_A) != (sk_A))
% 0.47/0.67        | ((sk_B) != (k5_relat_1 @ sk_B @ sk_C))
% 0.47/0.67        | ((k6_partfun1 @ sk_A) = (sk_C))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['78', '103'])).
% 0.47/0.67  thf('105', plain, (((k5_relat_1 @ sk_B @ sk_C) = (sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.67  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('108', plain,
% 0.47/0.67      ((((sk_A) != (sk_A))
% 0.47/0.67        | ((sk_B) != (sk_B))
% 0.47/0.67        | ((k6_partfun1 @ sk_A) = (sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.47/0.67  thf('109', plain, (((k6_partfun1 @ sk_A) = (sk_C))),
% 0.47/0.67      inference('simplify', [status(thm)], ['108'])).
% 0.47/0.67  thf('110', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('111', plain,
% 0.47/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.47/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.47/0.67          | (r2_relset_1 @ X36 @ X37 @ X35 @ X38)
% 0.47/0.67          | ((X35) != (X38)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.47/0.67  thf('112', plain,
% 0.47/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.67         ((r2_relset_1 @ X36 @ X37 @ X38 @ X38)
% 0.47/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['111'])).
% 0.47/0.67  thf('113', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['110', '112'])).
% 0.47/0.67  thf('114', plain, ($false),
% 0.47/0.67      inference('demod', [status(thm)], ['0', '109', '113'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
