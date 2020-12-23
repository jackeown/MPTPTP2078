%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSA9DgsctV

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:48 EST 2020

% Result     : Theorem 5.82s
% Output     : Refutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :  265 (26052 expanded)
%              Number of leaves         :   47 (7883 expanded)
%              Depth                    :   24
%              Number of atoms          : 2750 (535163 expanded)
%              Number of equality atoms :  108 (7645 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X65: $i,X66: $i] :
      ( ( ( k1_relset_1 @ X65 @ X65 @ X66 )
        = X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X65 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X63 ) @ X64 )
      | ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X63 ) @ X64 ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

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
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('27',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X63 ) @ X64 )
      | ( v1_funct_2 @ X63 @ ( k1_relat_1 @ X63 ) @ X64 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','32','35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('46',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X62 @ X61 @ X60 )
       != X61 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X62 @ X61 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('50',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('53',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('66',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('67',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('77',plain,(
    r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('81',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('85',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('86',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 )
      | ( X32 != X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('87',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','88'])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','94'])).

thf('96',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('100',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('107',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ ( k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ ( k6_partfun1 @ X51 ) @ X53 ) @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('108',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ ( k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ ( k6_relat_1 @ X51 ) @ X53 ) @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('113',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','96'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('120',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('127',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['105','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('145',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('156',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['145','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['142','161'])).

thf('163',plain,(
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

thf('164',plain,(
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

thf('165',plain,(
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
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
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
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,(
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
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
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
    inference('sup-',[status(thm)],['162','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('179',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('181',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','96'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('182',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('186',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','96'])).

thf('190',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','179','180','188','189'])).

thf('191',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('192',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf('194',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('195',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('196',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','192','193','194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('199',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('201',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf('203',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('204',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('205',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['204'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('206',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('207',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf('208',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['190','191'])).

thf('209',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['204'])).

thf('210',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['201','202','203','205','206','207','208','209'])).

thf('211',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('212',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('213',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X33 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    $false ),
    inference(demod,[status(thm)],['196','210','215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSA9DgsctV
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:12:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.82/6.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.82/6.03  % Solved by: fo/fo7.sh
% 5.82/6.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.82/6.03  % done 8154 iterations in 5.571s
% 5.82/6.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.82/6.03  % SZS output start Refutation
% 5.82/6.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.82/6.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.82/6.03  thf(sk_C_type, type, sk_C: $i).
% 5.82/6.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.82/6.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.82/6.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.82/6.03  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 5.82/6.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.82/6.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.82/6.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.82/6.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.82/6.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.82/6.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.82/6.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.82/6.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.82/6.03  thf(sk_B_type, type, sk_B: $i).
% 5.82/6.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.82/6.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.82/6.03  thf(sk_A_type, type, sk_A: $i).
% 5.82/6.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.82/6.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.82/6.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.82/6.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.82/6.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.82/6.03  thf(t76_funct_2, conjecture,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.82/6.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.82/6.03       ( ![C:$i]:
% 5.82/6.03         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.82/6.03             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.82/6.03           ( ( ( r2_relset_1 @
% 5.82/6.03                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 5.82/6.03               ( v2_funct_1 @ B ) ) =>
% 5.82/6.03             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 5.82/6.03  thf(zf_stmt_0, negated_conjecture,
% 5.82/6.03    (~( ![A:$i,B:$i]:
% 5.82/6.03        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.82/6.03            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.82/6.03          ( ![C:$i]:
% 5.82/6.03            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.82/6.03                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.82/6.03              ( ( ( r2_relset_1 @
% 5.82/6.03                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 5.82/6.03                  ( v2_funct_1 @ B ) ) =>
% 5.82/6.03                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 5.82/6.03    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 5.82/6.03  thf('0', plain,
% 5.82/6.03      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(redefinition_k6_partfun1, axiom,
% 5.82/6.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.82/6.03  thf('1', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.82/6.03  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['0', '1'])).
% 5.82/6.03  thf('3', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(t67_funct_2, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.82/6.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.82/6.03       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 5.82/6.03  thf('4', plain,
% 5.82/6.03      (![X65 : $i, X66 : $i]:
% 5.82/6.03         (((k1_relset_1 @ X65 @ X65 @ X66) = (X65))
% 5.82/6.03          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X65)))
% 5.82/6.03          | ~ (v1_funct_2 @ X66 @ X65 @ X65)
% 5.82/6.03          | ~ (v1_funct_1 @ X66))),
% 5.82/6.03      inference('cnf', [status(esa)], [t67_funct_2])).
% 5.82/6.03  thf('5', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.82/6.03        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['3', '4'])).
% 5.82/6.03  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('7', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('8', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(redefinition_k1_relset_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.82/6.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.82/6.03  thf('9', plain,
% 5.82/6.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.82/6.03         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 5.82/6.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.82/6.03  thf('10', plain,
% 5.82/6.03      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '9'])).
% 5.82/6.03  thf('11', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 5.82/6.03  thf(d10_xboole_0, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.82/6.03  thf('12', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.82/6.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.82/6.03  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.82/6.03      inference('simplify', [status(thm)], ['12'])).
% 5.82/6.03  thf(t4_funct_2, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.82/6.03       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 5.82/6.03         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 5.82/6.03           ( m1_subset_1 @
% 5.82/6.03             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 5.82/6.03  thf('14', plain,
% 5.82/6.03      (![X63 : $i, X64 : $i]:
% 5.82/6.03         (~ (r1_tarski @ (k2_relat_1 @ X63) @ X64)
% 5.82/6.03          | (m1_subset_1 @ X63 @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X63) @ X64)))
% 5.82/6.03          | ~ (v1_funct_1 @ X63)
% 5.82/6.03          | ~ (v1_relat_1 @ X63))),
% 5.82/6.03      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.82/6.03  thf('15', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_relat_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | (m1_subset_1 @ X0 @ 
% 5.82/6.03             (k1_zfmisc_1 @ 
% 5.82/6.03              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['13', '14'])).
% 5.82/6.03  thf('16', plain,
% 5.82/6.03      (((m1_subset_1 @ sk_B @ 
% 5.82/6.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 5.82/6.03        | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup+', [status(thm)], ['11', '15'])).
% 5.82/6.03  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('18', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(cc1_relset_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.82/6.03       ( v1_relat_1 @ C ) ))).
% 5.82/6.03  thf('19', plain,
% 5.82/6.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.82/6.03         ((v1_relat_1 @ X17)
% 5.82/6.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.82/6.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.82/6.03  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['18', '19'])).
% 5.82/6.03  thf('21', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 5.82/6.03      inference('demod', [status(thm)], ['16', '17', '20'])).
% 5.82/6.03  thf(t31_funct_2, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.82/6.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.82/6.03       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.82/6.03         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.82/6.03           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.82/6.03           ( m1_subset_1 @
% 5.82/6.03             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.82/6.03  thf('22', plain,
% 5.82/6.03      (![X60 : $i, X61 : $i, X62 : $i]:
% 5.82/6.03         (~ (v2_funct_1 @ X60)
% 5.82/6.03          | ((k2_relset_1 @ X62 @ X61 @ X60) != (X61))
% 5.82/6.03          | (m1_subset_1 @ (k2_funct_1 @ X60) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 5.82/6.03          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61)))
% 5.82/6.03          | ~ (v1_funct_2 @ X60 @ X62 @ X61)
% 5.82/6.03          | ~ (v1_funct_1 @ X60))),
% 5.82/6.03      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.82/6.03  thf('23', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 5.82/6.03        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 5.82/6.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 5.82/6.03        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 5.82/6.03            != (k2_relat_1 @ sk_B))
% 5.82/6.03        | ~ (v2_funct_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['21', '22'])).
% 5.82/6.03  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('25', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 5.82/6.03  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.82/6.03      inference('simplify', [status(thm)], ['12'])).
% 5.82/6.03  thf('27', plain,
% 5.82/6.03      (![X63 : $i, X64 : $i]:
% 5.82/6.03         (~ (r1_tarski @ (k2_relat_1 @ X63) @ X64)
% 5.82/6.03          | (v1_funct_2 @ X63 @ (k1_relat_1 @ X63) @ X64)
% 5.82/6.03          | ~ (v1_funct_1 @ X63)
% 5.82/6.03          | ~ (v1_relat_1 @ X63))),
% 5.82/6.03      inference('cnf', [status(esa)], [t4_funct_2])).
% 5.82/6.03  thf('28', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_relat_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['26', '27'])).
% 5.82/6.03  thf('29', plain,
% 5.82/6.03      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 5.82/6.03        | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup+', [status(thm)], ['25', '28'])).
% 5.82/6.03  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['18', '19'])).
% 5.82/6.03  thf('32', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['29', '30', '31'])).
% 5.82/6.03  thf('33', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 5.82/6.03      inference('demod', [status(thm)], ['16', '17', '20'])).
% 5.82/6.03  thf(redefinition_k2_relset_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.82/6.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.82/6.03  thf('34', plain,
% 5.82/6.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.82/6.03         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 5.82/6.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.82/6.03  thf('35', plain,
% 5.82/6.03      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['33', '34'])).
% 5.82/6.03  thf('36', plain, ((v2_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('37', plain,
% 5.82/6.03      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 5.82/6.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 5.82/6.03        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['23', '24', '32', '35', '36'])).
% 5.82/6.03  thf('38', plain,
% 5.82/6.03      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['37'])).
% 5.82/6.03  thf('39', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(dt_k1_partfun1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ E ) & 
% 5.82/6.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.82/6.03         ( v1_funct_1 @ F ) & 
% 5.82/6.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.82/6.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.82/6.03         ( m1_subset_1 @
% 5.82/6.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.82/6.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.82/6.03  thf('40', plain,
% 5.82/6.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.82/6.03          | ~ (v1_funct_1 @ X36)
% 5.82/6.03          | ~ (v1_funct_1 @ X39)
% 5.82/6.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 5.82/6.03          | (v1_funct_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)))),
% 5.82/6.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.82/6.03  thf('41', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['39', '40'])).
% 5.82/6.03  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('43', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0))),
% 5.82/6.03      inference('demod', [status(thm)], ['41', '42'])).
% 5.82/6.03  thf('44', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 5.82/6.03        | (v1_funct_1 @ 
% 5.82/6.03           (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 5.82/6.03            (k2_funct_1 @ sk_B))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['38', '43'])).
% 5.82/6.03  thf('45', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 5.82/6.03      inference('demod', [status(thm)], ['16', '17', '20'])).
% 5.82/6.03  thf('46', plain,
% 5.82/6.03      (![X60 : $i, X61 : $i, X62 : $i]:
% 5.82/6.03         (~ (v2_funct_1 @ X60)
% 5.82/6.03          | ((k2_relset_1 @ X62 @ X61 @ X60) != (X61))
% 5.82/6.03          | (v1_funct_1 @ (k2_funct_1 @ X60))
% 5.82/6.03          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61)))
% 5.82/6.03          | ~ (v1_funct_2 @ X60 @ X62 @ X61)
% 5.82/6.03          | ~ (v1_funct_1 @ X60))),
% 5.82/6.03      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.82/6.03  thf('47', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 5.82/6.03        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 5.82/6.03        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 5.82/6.03            != (k2_relat_1 @ sk_B))
% 5.82/6.03        | ~ (v2_funct_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['45', '46'])).
% 5.82/6.03  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['29', '30', '31'])).
% 5.82/6.03  thf('50', plain, ((v2_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('51', plain,
% 5.82/6.03      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 5.82/6.03        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 5.82/6.03            != (k2_relat_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 5.82/6.03  thf('52', plain,
% 5.82/6.03      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['33', '34'])).
% 5.82/6.03  thf('53', plain,
% 5.82/6.03      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 5.82/6.03        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['51', '52'])).
% 5.82/6.03  thf('54', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 5.82/6.03      inference('simplify', [status(thm)], ['53'])).
% 5.82/6.03  thf('55', plain,
% 5.82/6.03      ((v1_funct_1 @ 
% 5.82/6.03        (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 5.82/6.03         (k2_funct_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['44', '54'])).
% 5.82/6.03  thf('56', plain,
% 5.82/6.03      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['37'])).
% 5.82/6.03  thf('57', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(redefinition_k1_partfun1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ E ) & 
% 5.82/6.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.82/6.03         ( v1_funct_1 @ F ) & 
% 5.82/6.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.82/6.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.82/6.03  thf('58', plain,
% 5.82/6.03      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.82/6.03          | ~ (v1_funct_1 @ X44)
% 5.82/6.03          | ~ (v1_funct_1 @ X47)
% 5.82/6.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 5.82/6.03          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 5.82/6.03              = (k5_relat_1 @ X44 @ X47)))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.82/6.03  thf('59', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 5.82/6.03            = (k5_relat_1 @ sk_B @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['57', '58'])).
% 5.82/6.03  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('61', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 5.82/6.03            = (k5_relat_1 @ sk_B @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0))),
% 5.82/6.03      inference('demod', [status(thm)], ['59', '60'])).
% 5.82/6.03  thf('62', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 5.82/6.03        | ((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 5.82/6.03            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['56', '61'])).
% 5.82/6.03  thf('63', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 5.82/6.03      inference('simplify', [status(thm)], ['53'])).
% 5.82/6.03  thf('64', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 5.82/6.03  thf(t61_funct_1, axiom,
% 5.82/6.03    (![A:$i]:
% 5.82/6.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.82/6.03       ( ( v2_funct_1 @ A ) =>
% 5.82/6.03         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 5.82/6.03             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 5.82/6.03           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 5.82/6.03             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.82/6.03  thf('65', plain,
% 5.82/6.03      (![X16 : $i]:
% 5.82/6.03         (~ (v2_funct_1 @ X16)
% 5.82/6.03          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 5.82/6.03              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 5.82/6.03          | ~ (v1_funct_1 @ X16)
% 5.82/6.03          | ~ (v1_relat_1 @ X16))),
% 5.82/6.03      inference('cnf', [status(esa)], [t61_funct_1])).
% 5.82/6.03  thf(dt_k6_partfun1, axiom,
% 5.82/6.03    (![A:$i]:
% 5.82/6.03     ( ( m1_subset_1 @
% 5.82/6.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.82/6.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.82/6.03  thf('66', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.82/6.03  thf('67', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.82/6.03  thf('68', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf(t3_subset, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.82/6.03  thf('69', plain,
% 5.82/6.03      (![X7 : $i, X8 : $i]:
% 5.82/6.03         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_subset])).
% 5.82/6.03  thf('70', plain,
% 5.82/6.03      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['68', '69'])).
% 5.82/6.03  thf('71', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r1_tarski @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 5.82/6.03           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 5.82/6.03          | ~ (v1_relat_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v2_funct_1 @ X0))),
% 5.82/6.03      inference('sup+', [status(thm)], ['65', '70'])).
% 5.82/6.03  thf('72', plain,
% 5.82/6.03      (((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 5.82/6.03         (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 5.82/6.03        | ~ (v2_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v1_relat_1 @ sk_B))),
% 5.82/6.03      inference('sup+', [status(thm)], ['64', '71'])).
% 5.82/6.03  thf('73', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 5.82/6.03  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['18', '19'])).
% 5.82/6.03  thf('77', plain,
% 5.82/6.03      ((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 5.82/6.03        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 5.82/6.03  thf('78', plain,
% 5.82/6.03      (![X7 : $i, X9 : $i]:
% 5.82/6.03         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_subset])).
% 5.82/6.03  thf('79', plain,
% 5.82/6.03      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['77', '78'])).
% 5.82/6.03  thf('80', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf(redefinition_r2_relset_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i,D:$i]:
% 5.82/6.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.82/6.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.82/6.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.82/6.03  thf('81', plain,
% 5.82/6.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ((X32) = (X35))
% 5.82/6.03          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.82/6.03  thf('82', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 5.82/6.03          | ((k6_relat_1 @ X0) = (X1))
% 5.82/6.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['80', '81'])).
% 5.82/6.03  thf('83', plain,
% 5.82/6.03      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 5.82/6.03        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 5.82/6.03             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['79', '82'])).
% 5.82/6.03  thf('84', plain,
% 5.82/6.03      (![X16 : $i]:
% 5.82/6.03         (~ (v2_funct_1 @ X16)
% 5.82/6.03          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 5.82/6.03              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 5.82/6.03          | ~ (v1_funct_1 @ X16)
% 5.82/6.03          | ~ (v1_relat_1 @ X16))),
% 5.82/6.03      inference('cnf', [status(esa)], [t61_funct_1])).
% 5.82/6.03  thf('85', plain,
% 5.82/6.03      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['77', '78'])).
% 5.82/6.03  thf('86', plain,
% 5.82/6.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | (r2_relset_1 @ X33 @ X34 @ X32 @ X35)
% 5.82/6.03          | ((X32) != (X35)))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.82/6.03  thf('87', plain,
% 5.82/6.03      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 5.82/6.03      inference('simplify', [status(thm)], ['86'])).
% 5.82/6.03  thf('88', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.82/6.03        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 5.82/6.03        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['85', '87'])).
% 5.82/6.03  thf('89', plain,
% 5.82/6.03      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 5.82/6.03         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 5.82/6.03        | ~ (v1_relat_1 @ sk_B)
% 5.82/6.03        | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ~ (v2_funct_1 @ sk_B))),
% 5.82/6.03      inference('sup+', [status(thm)], ['84', '88'])).
% 5.82/6.03  thf('90', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 5.82/6.03  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['18', '19'])).
% 5.82/6.03  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('93', plain, ((v2_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('94', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 5.82/6.03        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 5.82/6.03  thf('95', plain,
% 5.82/6.03      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['83', '94'])).
% 5.82/6.03  thf('96', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 5.82/6.03         (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['62', '63', '95'])).
% 5.82/6.03  thf('97', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['55', '96'])).
% 5.82/6.03  thf('98', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('99', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf('100', plain,
% 5.82/6.03      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.82/6.03          | ~ (v1_funct_1 @ X44)
% 5.82/6.03          | ~ (v1_funct_1 @ X47)
% 5.82/6.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 5.82/6.03          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 5.82/6.03              = (k5_relat_1 @ X44 @ X47)))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.82/6.03  thf('101', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.82/6.03         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 5.82/6.03            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 5.82/6.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 5.82/6.03          | ~ (v1_funct_1 @ X1)
% 5.82/6.03          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['99', '100'])).
% 5.82/6.03  thf('102', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 5.82/6.03          | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 5.82/6.03              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['98', '101'])).
% 5.82/6.03  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('104', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 5.82/6.03          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 5.82/6.03              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 5.82/6.03      inference('demod', [status(thm)], ['102', '103'])).
% 5.82/6.03  thf('105', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 5.82/6.03         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['97', '104'])).
% 5.82/6.03  thf('106', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(t23_funct_2, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.82/6.03       ( ( r2_relset_1 @
% 5.82/6.03           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 5.82/6.03           C ) & 
% 5.82/6.03         ( r2_relset_1 @
% 5.82/6.03           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 5.82/6.03           C ) ) ))).
% 5.82/6.03  thf('107', plain,
% 5.82/6.03      (![X51 : $i, X52 : $i, X53 : $i]:
% 5.82/6.03         ((r2_relset_1 @ X51 @ X52 @ 
% 5.82/6.03           (k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ (k6_partfun1 @ X51) @ X53) @ 
% 5.82/6.03           X53)
% 5.82/6.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 5.82/6.03      inference('cnf', [status(esa)], [t23_funct_2])).
% 5.82/6.03  thf('108', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.82/6.03  thf('109', plain,
% 5.82/6.03      (![X51 : $i, X52 : $i, X53 : $i]:
% 5.82/6.03         ((r2_relset_1 @ X51 @ X52 @ 
% 5.82/6.03           (k4_relset_1 @ X51 @ X51 @ X51 @ X52 @ (k6_relat_1 @ X51) @ X53) @ 
% 5.82/6.03           X53)
% 5.82/6.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 5.82/6.03      inference('demod', [status(thm)], ['107', '108'])).
% 5.82/6.03  thf('110', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.82/6.03        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 5.82/6.03        sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['106', '109'])).
% 5.82/6.03  thf('111', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('112', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf(redefinition_k4_relset_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.82/6.03     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.82/6.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.82/6.03       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.82/6.03  thf('113', plain,
% 5.82/6.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.82/6.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 5.82/6.03          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 5.82/6.03              = (k5_relat_1 @ X26 @ X29)))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 5.82/6.03  thf('114', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.82/6.03         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 5.82/6.03            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 5.82/6.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['112', '113'])).
% 5.82/6.03  thf('115', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 5.82/6.03           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['111', '114'])).
% 5.82/6.03  thf('116', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.82/6.03        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 5.82/6.03      inference('demod', [status(thm)], ['110', '115'])).
% 5.82/6.03  thf('117', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['55', '96'])).
% 5.82/6.03  thf('118', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('119', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf('120', plain,
% 5.82/6.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.82/6.03          | ~ (v1_funct_1 @ X36)
% 5.82/6.03          | ~ (v1_funct_1 @ X39)
% 5.82/6.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 5.82/6.03          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 5.82/6.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.82/6.03  thf('121', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.82/6.03         ((m1_subset_1 @ 
% 5.82/6.03           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 5.82/6.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 5.82/6.03          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X2)
% 5.82/6.03          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['119', '120'])).
% 5.82/6.03  thf('122', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 5.82/6.03          | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03          | (m1_subset_1 @ 
% 5.82/6.03             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['118', '121'])).
% 5.82/6.03  thf('123', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('124', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 5.82/6.03          | (m1_subset_1 @ 
% 5.82/6.03             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 5.82/6.03      inference('demod', [status(thm)], ['122', '123'])).
% 5.82/6.03  thf('125', plain,
% 5.82/6.03      ((m1_subset_1 @ 
% 5.82/6.03        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['117', '124'])).
% 5.82/6.03  thf('126', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 5.82/6.03         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 5.82/6.03      inference('sup-', [status(thm)], ['97', '104'])).
% 5.82/6.03  thf('127', plain,
% 5.82/6.03      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('demod', [status(thm)], ['125', '126'])).
% 5.82/6.03  thf('128', plain,
% 5.82/6.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ((X32) = (X35))
% 5.82/6.03          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.82/6.03  thf('129', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.82/6.03             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 5.82/6.03          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['127', '128'])).
% 5.82/6.03  thf('130', plain,
% 5.82/6.03      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['116', '129'])).
% 5.82/6.03  thf('131', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('132', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['130', '131'])).
% 5.82/6.03  thf('133', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 5.82/6.03         = (sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['105', '132'])).
% 5.82/6.03  thf('134', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('135', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('136', plain,
% 5.82/6.03      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.82/6.03          | ~ (v1_funct_1 @ X44)
% 5.82/6.03          | ~ (v1_funct_1 @ X47)
% 5.82/6.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 5.82/6.03          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 5.82/6.03              = (k5_relat_1 @ X44 @ X47)))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.82/6.03  thf('137', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 5.82/6.03            = (k5_relat_1 @ sk_C @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_C))),
% 5.82/6.03      inference('sup-', [status(thm)], ['135', '136'])).
% 5.82/6.03  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('139', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 5.82/6.03            = (k5_relat_1 @ sk_C @ X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.82/6.03          | ~ (v1_funct_1 @ X0))),
% 5.82/6.03      inference('demod', [status(thm)], ['137', '138'])).
% 5.82/6.03  thf('140', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 5.82/6.03            = (k5_relat_1 @ sk_C @ sk_B)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['134', '139'])).
% 5.82/6.03  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('142', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 5.82/6.03         = (k5_relat_1 @ sk_C @ sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['140', '141'])).
% 5.82/6.03  thf('143', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.82/6.03        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('144', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 5.82/6.03         = (k5_relat_1 @ sk_C @ sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['140', '141'])).
% 5.82/6.03  thf('145', plain,
% 5.82/6.03      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 5.82/6.03      inference('demod', [status(thm)], ['143', '144'])).
% 5.82/6.03  thf('146', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('147', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('148', plain,
% 5.82/6.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.82/6.03          | ~ (v1_funct_1 @ X36)
% 5.82/6.03          | ~ (v1_funct_1 @ X39)
% 5.82/6.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 5.82/6.03          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 5.82/6.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.82/6.03  thf('149', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 5.82/6.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.82/6.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.82/6.03          | ~ (v1_funct_1 @ X1)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_C))),
% 5.82/6.03      inference('sup-', [status(thm)], ['147', '148'])).
% 5.82/6.03  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('151', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 5.82/6.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.82/6.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.82/6.03          | ~ (v1_funct_1 @ X1))),
% 5.82/6.03      inference('demod', [status(thm)], ['149', '150'])).
% 5.82/6.03  thf('152', plain,
% 5.82/6.03      ((~ (v1_funct_1 @ sk_B)
% 5.82/6.03        | (m1_subset_1 @ 
% 5.82/6.03           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 5.82/6.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['146', '151'])).
% 5.82/6.03  thf('153', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('154', plain,
% 5.82/6.03      ((m1_subset_1 @ 
% 5.82/6.03        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('demod', [status(thm)], ['152', '153'])).
% 5.82/6.03  thf('155', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 5.82/6.03         = (k5_relat_1 @ sk_C @ sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['140', '141'])).
% 5.82/6.03  thf('156', plain,
% 5.82/6.03      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 5.82/6.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('demod', [status(thm)], ['154', '155'])).
% 5.82/6.03  thf('157', plain,
% 5.82/6.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.82/6.03          | ((X32) = (X35))
% 5.82/6.03          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 5.82/6.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.82/6.03  thf('158', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 5.82/6.03          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['156', '157'])).
% 5.82/6.03  thf('159', plain,
% 5.82/6.03      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['145', '158'])).
% 5.82/6.03  thf('160', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('161', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['159', '160'])).
% 5.82/6.03  thf('162', plain,
% 5.82/6.03      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 5.82/6.03      inference('demod', [status(thm)], ['142', '161'])).
% 5.82/6.03  thf('163', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf(t27_funct_2, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.82/6.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.82/6.03       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 5.82/6.03            ( ~( ( v2_funct_1 @ C ) <=>
% 5.82/6.03                 ( ![D:$i,E:$i]:
% 5.82/6.03                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 5.82/6.03                       ( m1_subset_1 @
% 5.82/6.03                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 5.82/6.03                     ( ![F:$i]:
% 5.82/6.03                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 5.82/6.03                           ( m1_subset_1 @
% 5.82/6.03                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 5.82/6.03                         ( ( r2_relset_1 @
% 5.82/6.03                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 5.82/6.03                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 5.82/6.03                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 5.82/6.03  thf('164', plain,
% 5.82/6.03      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 5.82/6.03         (((X54) = (k1_xboole_0))
% 5.82/6.03          | ((X55) = (k1_xboole_0))
% 5.82/6.03          | ~ (v1_funct_1 @ X56)
% 5.82/6.03          | ~ (v1_funct_2 @ X56 @ X55 @ X54)
% 5.82/6.03          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 5.82/6.03          | ~ (v1_funct_1 @ X57)
% 5.82/6.03          | ~ (v1_funct_2 @ X57 @ X58 @ X55)
% 5.82/6.03          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 5.82/6.03          | ~ (r2_relset_1 @ X58 @ X54 @ 
% 5.82/6.03               (k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X57 @ X56) @ 
% 5.82/6.03               (k1_partfun1 @ X58 @ X55 @ X55 @ X54 @ X59 @ X56))
% 5.82/6.03          | (r2_relset_1 @ X58 @ X55 @ X57 @ X59)
% 5.82/6.03          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 5.82/6.03          | ~ (v1_funct_2 @ X59 @ X58 @ X55)
% 5.82/6.03          | ~ (v1_funct_1 @ X59)
% 5.82/6.03          | ~ (v2_funct_1 @ X56))),
% 5.82/6.03      inference('cnf', [status(esa)], [t27_funct_2])).
% 5.82/6.03  thf('165', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (~ (v2_funct_1 @ sk_B)
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 5.82/6.03          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 5.82/6.03          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 5.82/6.03          | ~ (v1_funct_1 @ X2)
% 5.82/6.03          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_B)
% 5.82/6.03          | ((sk_A) = (k1_xboole_0))
% 5.82/6.03          | ((sk_A) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['163', '164'])).
% 5.82/6.03  thf('166', plain, ((v2_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('167', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('168', plain, ((v1_funct_1 @ sk_B)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('169', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 5.82/6.03          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 5.82/6.03          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 5.82/6.03          | ~ (v1_funct_1 @ X2)
% 5.82/6.03          | ((sk_A) = (k1_xboole_0))
% 5.82/6.03          | ((sk_A) = (k1_xboole_0)))),
% 5.82/6.03      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 5.82/6.03  thf('170', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((sk_A) = (k1_xboole_0))
% 5.82/6.03          | ~ (v1_funct_1 @ X2)
% 5.82/6.03          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 5.82/6.03          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 5.82/6.03               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 5.82/6.03          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 5.82/6.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 5.82/6.03          | ~ (v1_funct_1 @ X0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['169'])).
% 5.82/6.03  thf('171', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 5.82/6.03             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 5.82/6.03          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 5.82/6.03          | ~ (v1_funct_1 @ sk_C)
% 5.82/6.03          | ((sk_A) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['162', '170'])).
% 5.82/6.03  thf('172', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('173', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('175', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 5.82/6.03             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.82/6.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 5.82/6.03          | ((sk_A) = (k1_xboole_0)))),
% 5.82/6.03      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 5.82/6.03  thf('176', plain,
% 5.82/6.03      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 5.82/6.03        | ((sk_A) = (k1_xboole_0))
% 5.82/6.03        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 5.82/6.03        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 5.82/6.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.82/6.03        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 5.82/6.03        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['133', '175'])).
% 5.82/6.03  thf('177', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('178', plain,
% 5.82/6.03      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 5.82/6.03      inference('simplify', [status(thm)], ['86'])).
% 5.82/6.03  thf('179', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 5.82/6.03      inference('sup-', [status(thm)], ['177', '178'])).
% 5.82/6.03  thf('180', plain,
% 5.82/6.03      (![X43 : $i]:
% 5.82/6.03         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 5.82/6.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf('181', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['55', '96'])).
% 5.82/6.03  thf(t71_relat_1, axiom,
% 5.82/6.03    (![A:$i]:
% 5.82/6.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.82/6.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.82/6.03  thf('182', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 5.82/6.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.82/6.03  thf('183', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (v1_relat_1 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ X0)
% 5.82/6.03          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['26', '27'])).
% 5.82/6.03  thf('184', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 5.82/6.03           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 5.82/6.03          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 5.82/6.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 5.82/6.03      inference('sup+', [status(thm)], ['182', '183'])).
% 5.82/6.03  thf('185', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 5.82/6.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.82/6.03  thf(fc4_funct_1, axiom,
% 5.82/6.03    (![A:$i]:
% 5.82/6.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.82/6.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.82/6.03  thf('186', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 5.82/6.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.82/6.03  thf('187', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 5.82/6.03          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 5.82/6.03      inference('demod', [status(thm)], ['184', '185', '186'])).
% 5.82/6.03  thf('188', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 5.82/6.03      inference('sup-', [status(thm)], ['181', '187'])).
% 5.82/6.03  thf('189', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['55', '96'])).
% 5.82/6.03  thf('190', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))
% 5.82/6.03        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 5.82/6.03      inference('demod', [status(thm)], ['176', '179', '180', '188', '189'])).
% 5.82/6.03  thf('191', plain,
% 5.82/6.03      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 5.82/6.03      inference('demod', [status(thm)], ['0', '1'])).
% 5.82/6.03  thf('192', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf('193', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf('194', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 5.82/6.03  thf('195', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.82/6.03      inference('cnf', [status(esa)], [t81_relat_1])).
% 5.82/6.03  thf('196', plain,
% 5.82/6.03      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 5.82/6.03      inference('demod', [status(thm)], ['2', '192', '193', '194', '195'])).
% 5.82/6.03  thf('197', plain,
% 5.82/6.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('198', plain,
% 5.82/6.03      (![X7 : $i, X8 : $i]:
% 5.82/6.03         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_subset])).
% 5.82/6.03  thf('199', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.82/6.03      inference('sup-', [status(thm)], ['197', '198'])).
% 5.82/6.03  thf('200', plain,
% 5.82/6.03      (![X0 : $i, X2 : $i]:
% 5.82/6.03         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.82/6.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.82/6.03  thf('201', plain,
% 5.82/6.03      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 5.82/6.03        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['199', '200'])).
% 5.82/6.03  thf('202', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf('203', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf(t113_zfmisc_1, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.82/6.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.82/6.03  thf('204', plain,
% 5.82/6.03      (![X5 : $i, X6 : $i]:
% 5.82/6.03         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 5.82/6.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.82/6.03  thf('205', plain,
% 5.82/6.03      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['204'])).
% 5.82/6.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.82/6.03  thf('206', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.82/6.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.82/6.03  thf('207', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf('208', plain, (((sk_A) = (k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['190', '191'])).
% 5.82/6.03  thf('209', plain,
% 5.82/6.03      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['204'])).
% 5.82/6.03  thf('210', plain, (((k1_xboole_0) = (sk_C))),
% 5.82/6.03      inference('demod', [status(thm)],
% 5.82/6.03                ['201', '202', '203', '205', '206', '207', '208', '209'])).
% 5.82/6.03  thf('211', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.82/6.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.82/6.03  thf('212', plain,
% 5.82/6.03      (![X7 : $i, X9 : $i]:
% 5.82/6.03         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_subset])).
% 5.82/6.03  thf('213', plain,
% 5.82/6.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['211', '212'])).
% 5.82/6.03  thf('214', plain,
% 5.82/6.03      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.82/6.03         ((r2_relset_1 @ X33 @ X34 @ X35 @ X35)
% 5.82/6.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 5.82/6.03      inference('simplify', [status(thm)], ['86'])).
% 5.82/6.03  thf('215', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['213', '214'])).
% 5.82/6.03  thf('216', plain, ($false),
% 5.82/6.03      inference('demod', [status(thm)], ['196', '210', '215'])).
% 5.82/6.03  
% 5.82/6.03  % SZS output end Refutation
% 5.82/6.03  
% 5.82/6.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
