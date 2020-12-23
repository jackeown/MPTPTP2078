%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K7rmoQ301q

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:50 EST 2020

% Result     : Theorem 10.23s
% Output     : Refutation 10.23s
% Verified   : 
% Statistics : Number of formulae       :  250 (20604 expanded)
%              Number of leaves         :   46 (6328 expanded)
%              Depth                    :   25
%              Number of atoms          : 2563 (426828 expanded)
%              Number of equality atoms :  103 (5100 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k1_relset_1 @ X64 @ X64 @ X65 )
        = X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X64 ) ) )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X64 )
      | ~ ( v1_funct_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X63: $i] :
      ( ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','19','20'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X62 @ X61 @ X60 )
       != X61 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X60 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X62 @ X61 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('26',plain,(
    ! [X63: $i] :
      ( ( v1_funct_2 @ X63 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','19','20'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','30','33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','19','20'])).

thf('44',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X62 @ X61 @ X60 )
       != X61 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X62 @ X61 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['50'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','61'])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('70',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('71',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('80',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ ( k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ ( k6_partfun1 @ X51 ) @ X53 ) @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('81',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ ( k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ ( k6_relat_1 @ X51 ) @ X53 ) @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('93',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('100',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('101',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['78','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('118',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('128',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['118','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['115','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( v2_funct_1 @ C )
            <=> ! [D: $i,E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ D @ A )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ D @ A )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                     => ( ( r2_relset_1 @ D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) )
                       => ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) )).

thf('136',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X55 @ X54 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X55 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X55 ) ) )
      | ~ ( r2_relset_1 @ X58 @ X54 @ ( k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X57 @ X56 ) @ ( k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X59 @ X56 ) )
      | ( r2_relset_1 @ X58 @ X55 @ X57 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X59 @ X58 @ X55 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v2_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 )
      | ( X32 != X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('151',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['149','151'])).

thf('153',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('154',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('155',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('156',plain,(
    ! [X63: $i] :
      ( ( v1_funct_2 @ X63 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('159',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('160',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158','163'])).

thf('165',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['154','164'])).

thf('166',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('167',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','152','153','165','166'])).

thf('168',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('169',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('171',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('172',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('173',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('175',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('176',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('177',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['175','176'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('178',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('179',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('180',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['177','182'])).

thf('184',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','169','170','171','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('187',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('189',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('191',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('192',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('193',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('195',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('196',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['167','168'])).

thf('197',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('198',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['189','190','191','193','194','195','196','197'])).

thf('199',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('200',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference(demod,[status(thm)],['184','198','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K7rmoQ301q
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.23/10.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.23/10.45  % Solved by: fo/fo7.sh
% 10.23/10.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.23/10.45  % done 12831 iterations in 9.987s
% 10.23/10.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.23/10.45  % SZS output start Refutation
% 10.23/10.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.23/10.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.23/10.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.23/10.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.23/10.45  thf(sk_C_type, type, sk_C: $i).
% 10.23/10.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 10.23/10.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.23/10.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.23/10.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.23/10.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.23/10.45  thf(sk_A_type, type, sk_A: $i).
% 10.23/10.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.23/10.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.23/10.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.23/10.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.23/10.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.23/10.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.23/10.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.23/10.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.23/10.45  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 10.23/10.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.23/10.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.23/10.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 10.23/10.45  thf(sk_B_type, type, sk_B: $i).
% 10.23/10.45  thf(t76_funct_2, conjecture,
% 10.23/10.45    (![A:$i,B:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.23/10.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.23/10.45       ( ![C:$i]:
% 10.23/10.45         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 10.23/10.45             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.23/10.45           ( ( ( r2_relset_1 @
% 10.23/10.45                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 10.23/10.45               ( v2_funct_1 @ B ) ) =>
% 10.23/10.45             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 10.23/10.45  thf(zf_stmt_0, negated_conjecture,
% 10.23/10.45    (~( ![A:$i,B:$i]:
% 10.23/10.45        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.23/10.45            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.23/10.45          ( ![C:$i]:
% 10.23/10.45            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 10.23/10.45                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.23/10.45              ( ( ( r2_relset_1 @
% 10.23/10.45                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 10.23/10.45                  ( v2_funct_1 @ B ) ) =>
% 10.23/10.45                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 10.23/10.45    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 10.23/10.45  thf('0', plain,
% 10.23/10.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(redefinition_k6_partfun1, axiom,
% 10.23/10.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.23/10.45  thf('1', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.45  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['0', '1'])).
% 10.23/10.45  thf(t61_funct_1, axiom,
% 10.23/10.45    (![A:$i]:
% 10.23/10.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.23/10.45       ( ( v2_funct_1 @ A ) =>
% 10.23/10.45         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 10.23/10.45             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 10.23/10.45           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 10.23/10.45             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.23/10.45  thf('3', plain,
% 10.23/10.45      (![X19 : $i]:
% 10.23/10.45         (~ (v2_funct_1 @ X19)
% 10.23/10.45          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 10.23/10.45              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 10.23/10.45          | ~ (v1_funct_1 @ X19)
% 10.23/10.45          | ~ (v1_relat_1 @ X19))),
% 10.23/10.45      inference('cnf', [status(esa)], [t61_funct_1])).
% 10.23/10.45  thf('4', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(t67_funct_2, axiom,
% 10.23/10.45    (![A:$i,B:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.23/10.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.23/10.45       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 10.23/10.45  thf('5', plain,
% 10.23/10.45      (![X64 : $i, X65 : $i]:
% 10.23/10.45         (((k1_relset_1 @ X64 @ X64 @ X65) = (X64))
% 10.23/10.45          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X64)))
% 10.23/10.45          | ~ (v1_funct_2 @ X65 @ X64 @ X64)
% 10.23/10.45          | ~ (v1_funct_1 @ X65))),
% 10.23/10.45      inference('cnf', [status(esa)], [t67_funct_2])).
% 10.23/10.45  thf('6', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 10.23/10.45        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['4', '5'])).
% 10.23/10.45  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('9', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(redefinition_k1_relset_1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i]:
% 10.23/10.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.23/10.45  thf('10', plain,
% 10.23/10.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.23/10.45         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 10.23/10.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.23/10.45  thf('11', plain,
% 10.23/10.45      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['9', '10'])).
% 10.23/10.45  thf('12', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 10.23/10.45  thf(t3_funct_2, axiom,
% 10.23/10.45    (![A:$i]:
% 10.23/10.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.23/10.45       ( ( v1_funct_1 @ A ) & 
% 10.23/10.45         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 10.23/10.45         ( m1_subset_1 @
% 10.23/10.45           A @ 
% 10.23/10.45           ( k1_zfmisc_1 @
% 10.23/10.45             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.23/10.45  thf('13', plain,
% 10.23/10.45      (![X63 : $i]:
% 10.23/10.45         ((m1_subset_1 @ X63 @ 
% 10.23/10.45           (k1_zfmisc_1 @ 
% 10.23/10.45            (k2_zfmisc_1 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63))))
% 10.23/10.45          | ~ (v1_funct_1 @ X63)
% 10.23/10.45          | ~ (v1_relat_1 @ X63))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.23/10.45  thf('14', plain,
% 10.23/10.45      (((m1_subset_1 @ sk_B @ 
% 10.23/10.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 10.23/10.45        | ~ (v1_relat_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup+', [status(thm)], ['12', '13'])).
% 10.23/10.45  thf('15', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(cc2_relat_1, axiom,
% 10.23/10.45    (![A:$i]:
% 10.23/10.45     ( ( v1_relat_1 @ A ) =>
% 10.23/10.45       ( ![B:$i]:
% 10.23/10.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.23/10.45  thf('16', plain,
% 10.23/10.45      (![X13 : $i, X14 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 10.23/10.45          | (v1_relat_1 @ X13)
% 10.23/10.45          | ~ (v1_relat_1 @ X14))),
% 10.23/10.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.23/10.45  thf('17', plain,
% 10.23/10.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['15', '16'])).
% 10.23/10.45  thf(fc6_relat_1, axiom,
% 10.23/10.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 10.23/10.45  thf('18', plain,
% 10.23/10.45      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 10.23/10.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.23/10.45  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 10.23/10.45      inference('demod', [status(thm)], ['17', '18'])).
% 10.23/10.45  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('21', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.23/10.45      inference('demod', [status(thm)], ['14', '19', '20'])).
% 10.23/10.45  thf(t31_funct_2, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.23/10.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 10.23/10.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 10.23/10.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 10.23/10.45           ( m1_subset_1 @
% 10.23/10.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 10.23/10.45  thf('22', plain,
% 10.23/10.45      (![X60 : $i, X61 : $i, X62 : $i]:
% 10.23/10.45         (~ (v2_funct_1 @ X60)
% 10.23/10.45          | ((k2_relset_1 @ X62 @ X61 @ X60) != (X61))
% 10.23/10.45          | (m1_subset_1 @ (k2_funct_1 @ X60) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 10.23/10.45          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61)))
% 10.23/10.45          | ~ (v1_funct_2 @ X60 @ X62 @ X61)
% 10.23/10.45          | ~ (v1_funct_1 @ X60))),
% 10.23/10.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.23/10.45  thf('23', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.23/10.45        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.23/10.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 10.23/10.45        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 10.23/10.45            != (k2_relat_1 @ sk_B))
% 10.23/10.45        | ~ (v2_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['21', '22'])).
% 10.23/10.45  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('25', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 10.23/10.45  thf('26', plain,
% 10.23/10.45      (![X63 : $i]:
% 10.23/10.45         ((v1_funct_2 @ X63 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63))
% 10.23/10.45          | ~ (v1_funct_1 @ X63)
% 10.23/10.45          | ~ (v1_relat_1 @ X63))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.23/10.45  thf('27', plain,
% 10.23/10.45      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.23/10.45        | ~ (v1_relat_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup+', [status(thm)], ['25', '26'])).
% 10.23/10.45  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 10.23/10.45      inference('demod', [status(thm)], ['17', '18'])).
% 10.23/10.45  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('30', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['27', '28', '29'])).
% 10.23/10.45  thf('31', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.23/10.45      inference('demod', [status(thm)], ['14', '19', '20'])).
% 10.23/10.45  thf(redefinition_k2_relset_1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i]:
% 10.23/10.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.23/10.45  thf('32', plain,
% 10.23/10.45      (![X23 : $i, X24 : $i, X25 : $i]:
% 10.23/10.45         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 10.23/10.45          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.23/10.45  thf('33', plain,
% 10.23/10.45      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['31', '32'])).
% 10.23/10.45  thf('34', plain, ((v2_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('35', plain,
% 10.23/10.45      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.23/10.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 10.23/10.45        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['23', '24', '30', '33', '34'])).
% 10.23/10.45  thf('36', plain,
% 10.23/10.45      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 10.23/10.45      inference('simplify', [status(thm)], ['35'])).
% 10.23/10.45  thf('37', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(dt_k1_partfun1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ E ) & 
% 10.23/10.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.45         ( v1_funct_1 @ F ) & 
% 10.23/10.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.23/10.45       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.23/10.45         ( m1_subset_1 @
% 10.23/10.45           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.23/10.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 10.23/10.45  thf('38', plain,
% 10.23/10.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 10.23/10.45          | ~ (v1_funct_1 @ X36)
% 10.23/10.45          | ~ (v1_funct_1 @ X39)
% 10.23/10.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 10.23/10.45          | (v1_funct_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)))),
% 10.23/10.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.23/10.45  thf('39', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['37', '38'])).
% 10.23/10.45  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('41', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0))),
% 10.23/10.45      inference('demod', [status(thm)], ['39', '40'])).
% 10.23/10.45  thf('42', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.23/10.45        | (v1_funct_1 @ 
% 10.23/10.45           (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 10.23/10.45            (k2_funct_1 @ sk_B))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['36', '41'])).
% 10.23/10.45  thf('43', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.23/10.45      inference('demod', [status(thm)], ['14', '19', '20'])).
% 10.23/10.45  thf('44', plain,
% 10.23/10.45      (![X60 : $i, X61 : $i, X62 : $i]:
% 10.23/10.45         (~ (v2_funct_1 @ X60)
% 10.23/10.45          | ((k2_relset_1 @ X62 @ X61 @ X60) != (X61))
% 10.23/10.45          | (v1_funct_1 @ (k2_funct_1 @ X60))
% 10.23/10.45          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61)))
% 10.23/10.45          | ~ (v1_funct_2 @ X60 @ X62 @ X61)
% 10.23/10.45          | ~ (v1_funct_1 @ X60))),
% 10.23/10.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.23/10.45  thf('45', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.23/10.45        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.23/10.45        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 10.23/10.45            != (k2_relat_1 @ sk_B))
% 10.23/10.45        | ~ (v2_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['43', '44'])).
% 10.23/10.45  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('47', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['27', '28', '29'])).
% 10.23/10.45  thf('48', plain,
% 10.23/10.45      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['31', '32'])).
% 10.23/10.45  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('50', plain,
% 10.23/10.45      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.23/10.45        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 10.23/10.45  thf('51', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 10.23/10.45      inference('simplify', [status(thm)], ['50'])).
% 10.23/10.45  thf('52', plain,
% 10.23/10.45      ((v1_funct_1 @ 
% 10.23/10.45        (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 10.23/10.45         (k2_funct_1 @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['42', '51'])).
% 10.23/10.45  thf('53', plain,
% 10.23/10.45      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 10.23/10.45      inference('simplify', [status(thm)], ['35'])).
% 10.23/10.45  thf('54', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(redefinition_k1_partfun1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ E ) & 
% 10.23/10.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.45         ( v1_funct_1 @ F ) & 
% 10.23/10.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.23/10.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.23/10.45  thf('55', plain,
% 10.23/10.45      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 10.23/10.45          | ~ (v1_funct_1 @ X44)
% 10.23/10.45          | ~ (v1_funct_1 @ X47)
% 10.23/10.45          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 10.23/10.45          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 10.23/10.45              = (k5_relat_1 @ X44 @ X47)))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.23/10.45  thf('56', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 10.23/10.45            = (k5_relat_1 @ sk_B @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['54', '55'])).
% 10.23/10.45  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('58', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 10.23/10.45            = (k5_relat_1 @ sk_B @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0))),
% 10.23/10.45      inference('demod', [status(thm)], ['56', '57'])).
% 10.23/10.45  thf('59', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.23/10.45        | ((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 10.23/10.45            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['53', '58'])).
% 10.23/10.45  thf('60', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 10.23/10.45      inference('simplify', [status(thm)], ['50'])).
% 10.23/10.45  thf('61', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 10.23/10.45         (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['59', '60'])).
% 10.23/10.45  thf('62', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['52', '61'])).
% 10.23/10.45  thf('63', plain,
% 10.23/10.45      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 10.23/10.45        | ~ (v1_relat_1 @ sk_B)
% 10.23/10.45        | ~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | ~ (v2_funct_1 @ sk_B))),
% 10.23/10.45      inference('sup+', [status(thm)], ['3', '62'])).
% 10.23/10.45  thf('64', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 10.23/10.45  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 10.23/10.45      inference('demod', [status(thm)], ['17', '18'])).
% 10.23/10.45  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('68', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 10.23/10.45  thf('69', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(dt_k6_partfun1, axiom,
% 10.23/10.45    (![A:$i]:
% 10.23/10.45     ( ( m1_subset_1 @
% 10.23/10.45         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 10.23/10.45       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 10.23/10.45  thf('70', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 10.23/10.45  thf('71', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.45  thf('72', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf('73', plain,
% 10.23/10.45      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 10.23/10.45          | ~ (v1_funct_1 @ X44)
% 10.23/10.45          | ~ (v1_funct_1 @ X47)
% 10.23/10.45          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 10.23/10.45          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 10.23/10.45              = (k5_relat_1 @ X44 @ X47)))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.23/10.45  thf('74', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.23/10.45         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 10.23/10.45            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 10.23/10.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.23/10.45          | ~ (v1_funct_1 @ X1)
% 10.23/10.45          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['72', '73'])).
% 10.23/10.45  thf('75', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.23/10.45          | ~ (v1_funct_1 @ sk_B)
% 10.23/10.45          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.23/10.45              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['69', '74'])).
% 10.23/10.45  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('77', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.23/10.45          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.23/10.45              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 10.23/10.45      inference('demod', [status(thm)], ['75', '76'])).
% 10.23/10.45  thf('78', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.23/10.45         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['68', '77'])).
% 10.23/10.45  thf('79', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(t23_funct_2, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i]:
% 10.23/10.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.45       ( ( r2_relset_1 @
% 10.23/10.45           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 10.23/10.45           C ) & 
% 10.23/10.45         ( r2_relset_1 @
% 10.23/10.45           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 10.23/10.45           C ) ) ))).
% 10.23/10.45  thf('80', plain,
% 10.23/10.45      (![X51 : $i, X52 : $i, X53 : $i]:
% 10.23/10.45         ((r2_relset_1 @ X51 @ X52 @ 
% 10.23/10.45           (k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ (k6_partfun1 @ X51) @ X53) @ 
% 10.23/10.45           X53)
% 10.23/10.45          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 10.23/10.45      inference('cnf', [status(esa)], [t23_funct_2])).
% 10.23/10.45  thf('81', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.45  thf('82', plain,
% 10.23/10.45      (![X51 : $i, X52 : $i, X53 : $i]:
% 10.23/10.45         ((r2_relset_1 @ X51 @ X52 @ 
% 10.23/10.45           (k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ (k6_relat_1 @ X51) @ X53) @ 
% 10.23/10.45           X53)
% 10.23/10.45          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 10.23/10.45      inference('demod', [status(thm)], ['80', '81'])).
% 10.23/10.45  thf('83', plain,
% 10.23/10.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.45        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.23/10.45        sk_B)),
% 10.23/10.45      inference('sup-', [status(thm)], ['79', '82'])).
% 10.23/10.45  thf('84', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('85', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf(redefinition_k4_relset_1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.23/10.45     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.23/10.45       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.23/10.45  thf('86', plain,
% 10.23/10.45      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 10.23/10.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 10.23/10.45          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 10.23/10.45              = (k5_relat_1 @ X26 @ X29)))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 10.23/10.45  thf('87', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.23/10.45         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 10.23/10.45            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 10.23/10.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['85', '86'])).
% 10.23/10.45  thf('88', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.23/10.45           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['84', '87'])).
% 10.23/10.45  thf('89', plain,
% 10.23/10.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.45        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 10.23/10.45      inference('demod', [status(thm)], ['83', '88'])).
% 10.23/10.45  thf('90', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 10.23/10.45  thf('91', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('92', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf('93', plain,
% 10.23/10.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 10.23/10.45          | ~ (v1_funct_1 @ X36)
% 10.23/10.45          | ~ (v1_funct_1 @ X39)
% 10.23/10.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 10.23/10.45          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 10.23/10.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.23/10.45  thf('94', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.23/10.45         ((m1_subset_1 @ 
% 10.23/10.45           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.23/10.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 10.23/10.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X2)
% 10.23/10.45          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['92', '93'])).
% 10.23/10.45  thf('95', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.23/10.45          | ~ (v1_funct_1 @ sk_B)
% 10.23/10.45          | (m1_subset_1 @ 
% 10.23/10.45             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['91', '94'])).
% 10.23/10.45  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('97', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.23/10.45          | (m1_subset_1 @ 
% 10.23/10.45             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 10.23/10.45      inference('demod', [status(thm)], ['95', '96'])).
% 10.23/10.45  thf('98', plain,
% 10.23/10.45      ((m1_subset_1 @ 
% 10.23/10.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['90', '97'])).
% 10.23/10.45  thf('99', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.23/10.45         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 10.23/10.45      inference('sup-', [status(thm)], ['68', '77'])).
% 10.23/10.45  thf('100', plain,
% 10.23/10.45      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('demod', [status(thm)], ['98', '99'])).
% 10.23/10.45  thf(redefinition_r2_relset_1, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i,D:$i]:
% 10.23/10.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.23/10.45  thf('101', plain,
% 10.23/10.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | ((X32) = (X35))
% 10.23/10.45          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.23/10.45  thf('102', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.45             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 10.23/10.45          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['100', '101'])).
% 10.23/10.45  thf('103', plain,
% 10.23/10.45      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['89', '102'])).
% 10.23/10.45  thf('104', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('105', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['103', '104'])).
% 10.23/10.45  thf('106', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.23/10.45         = (sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['78', '105'])).
% 10.23/10.45  thf('107', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('108', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('109', plain,
% 10.23/10.45      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 10.23/10.45          | ~ (v1_funct_1 @ X44)
% 10.23/10.45          | ~ (v1_funct_1 @ X47)
% 10.23/10.45          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 10.23/10.45          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 10.23/10.45              = (k5_relat_1 @ X44 @ X47)))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.23/10.45  thf('110', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 10.23/10.45            = (k5_relat_1 @ sk_C @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.45      inference('sup-', [status(thm)], ['108', '109'])).
% 10.23/10.45  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('112', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 10.23/10.45            = (k5_relat_1 @ sk_C @ X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.45          | ~ (v1_funct_1 @ X0))),
% 10.23/10.45      inference('demod', [status(thm)], ['110', '111'])).
% 10.23/10.45  thf('113', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.23/10.45            = (k5_relat_1 @ sk_C @ sk_B)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['107', '112'])).
% 10.23/10.45  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('115', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.23/10.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['113', '114'])).
% 10.23/10.45  thf('116', plain,
% 10.23/10.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('117', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.23/10.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['113', '114'])).
% 10.23/10.45  thf('118', plain,
% 10.23/10.45      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 10.23/10.45      inference('demod', [status(thm)], ['116', '117'])).
% 10.23/10.45  thf('119', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('120', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('121', plain,
% 10.23/10.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 10.23/10.45          | ~ (v1_funct_1 @ X36)
% 10.23/10.45          | ~ (v1_funct_1 @ X39)
% 10.23/10.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 10.23/10.45          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 10.23/10.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.23/10.45  thf('122', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 10.23/10.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.23/10.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.23/10.45          | ~ (v1_funct_1 @ X1)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.45      inference('sup-', [status(thm)], ['120', '121'])).
% 10.23/10.45  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('124', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 10.23/10.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.23/10.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.23/10.45          | ~ (v1_funct_1 @ X1))),
% 10.23/10.45      inference('demod', [status(thm)], ['122', '123'])).
% 10.23/10.45  thf('125', plain,
% 10.23/10.45      ((~ (v1_funct_1 @ sk_B)
% 10.23/10.45        | (m1_subset_1 @ 
% 10.23/10.45           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 10.23/10.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['119', '124'])).
% 10.23/10.45  thf('126', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('127', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.23/10.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['113', '114'])).
% 10.23/10.45  thf('128', plain,
% 10.23/10.45      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 10.23/10.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('demod', [status(thm)], ['125', '126', '127'])).
% 10.23/10.45  thf('129', plain,
% 10.23/10.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | ((X32) = (X35))
% 10.23/10.45          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.23/10.45  thf('130', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 10.23/10.45          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.23/10.45      inference('sup-', [status(thm)], ['128', '129'])).
% 10.23/10.45  thf('131', plain,
% 10.23/10.45      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['118', '130'])).
% 10.23/10.45  thf('132', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('133', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['131', '132'])).
% 10.23/10.45  thf('134', plain,
% 10.23/10.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 10.23/10.45      inference('demod', [status(thm)], ['115', '133'])).
% 10.23/10.45  thf('135', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf(t27_funct_2, axiom,
% 10.23/10.45    (![A:$i,B:$i,C:$i]:
% 10.23/10.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.23/10.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.45       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 10.23/10.45            ( ~( ( v2_funct_1 @ C ) <=>
% 10.23/10.45                 ( ![D:$i,E:$i]:
% 10.23/10.45                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 10.23/10.45                       ( m1_subset_1 @
% 10.23/10.45                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 10.23/10.45                     ( ![F:$i]:
% 10.23/10.45                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 10.23/10.45                           ( m1_subset_1 @
% 10.23/10.45                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 10.23/10.45                         ( ( r2_relset_1 @
% 10.23/10.45                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 10.23/10.45                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 10.23/10.45                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 10.23/10.45  thf('136', plain,
% 10.23/10.45      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 10.23/10.45         (((X54) = (k1_xboole_0))
% 10.23/10.45          | ((X55) = (k1_xboole_0))
% 10.23/10.45          | ~ (v1_funct_1 @ X56)
% 10.23/10.45          | ~ (v1_funct_2 @ X56 @ X55 @ X54)
% 10.23/10.45          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 10.23/10.45          | ~ (v1_funct_1 @ X57)
% 10.23/10.45          | ~ (v1_funct_2 @ X57 @ X58 @ X55)
% 10.23/10.45          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 10.23/10.45          | ~ (r2_relset_1 @ X58 @ X54 @ 
% 10.23/10.45               (k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X57 @ X56) @ 
% 10.23/10.45               (k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X59 @ X56))
% 10.23/10.45          | (r2_relset_1 @ X58 @ X55 @ X57 @ X59)
% 10.23/10.45          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 10.23/10.45          | ~ (v1_funct_2 @ X59 @ X58 @ X55)
% 10.23/10.45          | ~ (v1_funct_1 @ X59)
% 10.23/10.45          | ~ (v2_funct_1 @ X56))),
% 10.23/10.45      inference('cnf', [status(esa)], [t27_funct_2])).
% 10.23/10.45  thf('137', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (~ (v2_funct_1 @ sk_B)
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.23/10.45          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.23/10.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.23/10.45          | ~ (v1_funct_1 @ X2)
% 10.23/10.45          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_B)
% 10.23/10.45          | ((sk_A) = (k1_xboole_0))
% 10.23/10.45          | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['135', '136'])).
% 10.23/10.45  thf('138', plain, ((v2_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('139', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('140', plain, ((v1_funct_1 @ sk_B)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('141', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.23/10.45          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.23/10.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.23/10.45          | ~ (v1_funct_1 @ X2)
% 10.23/10.45          | ((sk_A) = (k1_xboole_0))
% 10.23/10.45          | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.45      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 10.23/10.45  thf('142', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.45         (((sk_A) = (k1_xboole_0))
% 10.23/10.45          | ~ (v1_funct_1 @ X2)
% 10.23/10.45          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.23/10.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.23/10.45               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.23/10.45          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.23/10.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.23/10.45          | ~ (v1_funct_1 @ X0))),
% 10.23/10.45      inference('simplify', [status(thm)], ['141'])).
% 10.23/10.45  thf('143', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 10.23/10.45             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 10.23/10.45          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 10.23/10.45          | ~ (v1_funct_1 @ sk_C)
% 10.23/10.45          | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['134', '142'])).
% 10.23/10.45  thf('144', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('147', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 10.23/10.45             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.23/10.45          | ~ (v1_funct_1 @ X0)
% 10.23/10.45          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 10.23/10.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 10.23/10.45          | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.45      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 10.23/10.45  thf('148', plain,
% 10.23/10.45      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 10.23/10.45        | ((sk_A) = (k1_xboole_0))
% 10.23/10.45        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 10.23/10.45        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 10.23/10.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.45        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 10.23/10.45        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['106', '147'])).
% 10.23/10.45  thf('149', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('150', plain,
% 10.23/10.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.23/10.45          | (r2_relset_1 @ X33 @ X34 @ X32 @ X35)
% 10.23/10.45          | ((X32) != (X35)))),
% 10.23/10.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.23/10.45  thf('151', plain,
% 10.23/10.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.23/10.45         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 10.23/10.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 10.23/10.45      inference('simplify', [status(thm)], ['150'])).
% 10.23/10.45  thf('152', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 10.23/10.45      inference('sup-', [status(thm)], ['149', '151'])).
% 10.23/10.45  thf('153', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf('154', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 10.23/10.45  thf(t71_relat_1, axiom,
% 10.23/10.45    (![A:$i]:
% 10.23/10.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.23/10.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.23/10.45  thf('155', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 10.23/10.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.23/10.45  thf('156', plain,
% 10.23/10.45      (![X63 : $i]:
% 10.23/10.45         ((v1_funct_2 @ X63 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63))
% 10.23/10.45          | ~ (v1_funct_1 @ X63)
% 10.23/10.45          | ~ (v1_relat_1 @ X63))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.23/10.45  thf('157', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 10.23/10.45           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 10.23/10.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.23/10.45          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.23/10.45      inference('sup+', [status(thm)], ['155', '156'])).
% 10.23/10.45  thf('158', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 10.23/10.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.23/10.45  thf('159', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf('160', plain,
% 10.23/10.45      (![X13 : $i, X14 : $i]:
% 10.23/10.45         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 10.23/10.45          | (v1_relat_1 @ X13)
% 10.23/10.45          | ~ (v1_relat_1 @ X14))),
% 10.23/10.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.23/10.45  thf('161', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 10.23/10.45          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['159', '160'])).
% 10.23/10.45  thf('162', plain,
% 10.23/10.45      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 10.23/10.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.23/10.45  thf('163', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 10.23/10.45      inference('demod', [status(thm)], ['161', '162'])).
% 10.23/10.45  thf('164', plain,
% 10.23/10.45      (![X0 : $i]:
% 10.23/10.45         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 10.23/10.45          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.23/10.45      inference('demod', [status(thm)], ['157', '158', '163'])).
% 10.23/10.45  thf('165', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 10.23/10.45      inference('sup-', [status(thm)], ['154', '164'])).
% 10.23/10.45  thf('166', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 10.23/10.45  thf('167', plain,
% 10.23/10.45      ((((sk_A) = (k1_xboole_0))
% 10.23/10.45        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 10.23/10.45      inference('demod', [status(thm)], ['148', '152', '153', '165', '166'])).
% 10.23/10.45  thf('168', plain,
% 10.23/10.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 10.23/10.45      inference('demod', [status(thm)], ['0', '1'])).
% 10.23/10.45  thf('169', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('170', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('171', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf(t113_zfmisc_1, axiom,
% 10.23/10.45    (![A:$i,B:$i]:
% 10.23/10.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.23/10.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.23/10.45  thf('172', plain,
% 10.23/10.45      (![X4 : $i, X5 : $i]:
% 10.23/10.45         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 10.23/10.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.23/10.45  thf('173', plain,
% 10.23/10.45      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 10.23/10.45      inference('simplify', [status(thm)], ['172'])).
% 10.23/10.45  thf('174', plain,
% 10.23/10.45      (![X43 : $i]:
% 10.23/10.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 10.23/10.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 10.23/10.45      inference('demod', [status(thm)], ['70', '71'])).
% 10.23/10.45  thf('175', plain,
% 10.23/10.45      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 10.23/10.45      inference('sup+', [status(thm)], ['173', '174'])).
% 10.23/10.45  thf(t3_subset, axiom,
% 10.23/10.45    (![A:$i,B:$i]:
% 10.23/10.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.23/10.45  thf('176', plain,
% 10.23/10.45      (![X7 : $i, X8 : $i]:
% 10.23/10.45         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_subset])).
% 10.23/10.45  thf('177', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 10.23/10.45      inference('sup-', [status(thm)], ['175', '176'])).
% 10.23/10.45  thf(t4_subset_1, axiom,
% 10.23/10.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 10.23/10.45  thf('178', plain,
% 10.23/10.45      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 10.23/10.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.23/10.45  thf('179', plain,
% 10.23/10.45      (![X7 : $i, X8 : $i]:
% 10.23/10.45         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_subset])).
% 10.23/10.45  thf('180', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.23/10.45      inference('sup-', [status(thm)], ['178', '179'])).
% 10.23/10.45  thf(d10_xboole_0, axiom,
% 10.23/10.45    (![A:$i,B:$i]:
% 10.23/10.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.23/10.45  thf('181', plain,
% 10.23/10.45      (![X0 : $i, X2 : $i]:
% 10.23/10.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.23/10.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.23/10.45  thf('182', plain,
% 10.23/10.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['180', '181'])).
% 10.23/10.45  thf('183', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.23/10.45      inference('sup-', [status(thm)], ['177', '182'])).
% 10.23/10.45  thf('184', plain,
% 10.23/10.45      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 10.23/10.45      inference('demod', [status(thm)], ['2', '169', '170', '171', '183'])).
% 10.23/10.45  thf('185', plain,
% 10.23/10.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.45  thf('186', plain,
% 10.23/10.45      (![X7 : $i, X8 : $i]:
% 10.23/10.45         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 10.23/10.45      inference('cnf', [status(esa)], [t3_subset])).
% 10.23/10.45  thf('187', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 10.23/10.45      inference('sup-', [status(thm)], ['185', '186'])).
% 10.23/10.45  thf('188', plain,
% 10.23/10.45      (![X0 : $i, X2 : $i]:
% 10.23/10.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.23/10.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.23/10.45  thf('189', plain,
% 10.23/10.45      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 10.23/10.45        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 10.23/10.45      inference('sup-', [status(thm)], ['187', '188'])).
% 10.23/10.45  thf('190', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('191', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('192', plain,
% 10.23/10.45      (![X4 : $i, X5 : $i]:
% 10.23/10.45         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 10.23/10.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.23/10.45  thf('193', plain,
% 10.23/10.45      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 10.23/10.45      inference('simplify', [status(thm)], ['192'])).
% 10.23/10.45  thf('194', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.23/10.45      inference('sup-', [status(thm)], ['178', '179'])).
% 10.23/10.45  thf('195', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('196', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.45      inference('clc', [status(thm)], ['167', '168'])).
% 10.23/10.45  thf('197', plain,
% 10.23/10.45      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 10.23/10.45      inference('simplify', [status(thm)], ['192'])).
% 10.23/10.45  thf('198', plain, (((k1_xboole_0) = (sk_C))),
% 10.23/10.45      inference('demod', [status(thm)],
% 10.23/10.45                ['189', '190', '191', '193', '194', '195', '196', '197'])).
% 10.23/10.45  thf('199', plain,
% 10.23/10.45      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 10.23/10.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.23/10.45  thf('200', plain,
% 10.23/10.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.23/10.45         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 10.23/10.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 10.23/10.45      inference('simplify', [status(thm)], ['150'])).
% 10.23/10.45  thf('201', plain,
% 10.23/10.45      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.23/10.45      inference('sup-', [status(thm)], ['199', '200'])).
% 10.23/10.45  thf('202', plain, ($false),
% 10.23/10.45      inference('demod', [status(thm)], ['184', '198', '201'])).
% 10.23/10.45  
% 10.23/10.45  % SZS output end Refutation
% 10.23/10.45  
% 10.23/10.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
