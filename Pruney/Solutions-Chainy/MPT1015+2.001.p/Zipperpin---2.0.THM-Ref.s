%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l3afOWLQAj

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:47 EST 2020

% Result     : Theorem 9.88s
% Output     : Refutation 9.88s
% Verified   : 
% Statistics : Number of formulae       :  254 (22323 expanded)
%              Number of leaves         :   46 (6733 expanded)
%              Depth                    :   25
%              Number of atoms          : 2618 (441842 expanded)
%              Number of equality atoms :  102 (5982 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ X14 @ ( k2_funct_1 @ X14 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X63: $i,X64: $i] :
      ( ( ( k1_relset_1 @ X63 @ X63 @ X64 )
        = X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X63 @ X63 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X61 ) @ X62 )
      | ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X61 ) @ X62 ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

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

thf('25',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X58 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('30',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X61 ) @ X62 )
      | ( v1_funct_2 @ X61 @ ( k1_relat_1 @ X61 ) @ X62 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('35',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','35','38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('49',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('53',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('56',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['56'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('76',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('77',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('86',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_relset_1 @ X49 @ X50 @ ( k4_relset_1 @ X49 @ X49 @ X49 @ X50 @ ( k6_partfun1 @ X49 ) @ X51 ) @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('87',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_relset_1 @ X49 @ X50 @ ( k4_relset_1 @ X49 @ X49 @ X49 @ X50 @ ( k6_relat_1 @ X49 ) @ X51 ) @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('99',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('106',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('107',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['84','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('124',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('135',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['124','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['121','140'])).

thf('142',plain,(
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

thf('143',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X53 ) ) )
      | ~ ( r2_relset_1 @ X56 @ X52 @ ( k1_partfun1 @ X56 @ X53 @ X53 @ X52 @ X55 @ X54 ) @ ( k1_partfun1 @ X56 @ X53 @ X53 @ X52 @ X57 @ X54 ) )
      | ( r2_relset_1 @ X56 @ X53 @ X55 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X53 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v2_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('144',plain,(
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
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
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
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
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
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
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
    inference('sup-',[status(thm)],['141','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('158',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['156','158'])).

thf('160',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('161',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('162',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('163',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_partfun1 @ X31 @ X32 )
      | ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_partfun1 @ ( k6_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X40: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X40 ) @ X40 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('166',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('167',plain,(
    ! [X40: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X40 ) @ X40 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['164','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['161','168'])).

thf('170',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('171',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','159','160','169','170'])).

thf('172',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('173',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('175',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('176',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('177',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('179',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('180',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('181',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['179','180'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('182',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('183',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','173','174','175','185'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('189',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('191',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('193',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('194',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('195',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('197',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('198',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['171','172'])).

thf('199',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['194'])).

thf('200',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['191','192','193','195','196','197','198','199'])).

thf('201',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('202',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('203',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['186','200','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l3afOWLQAj
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.88/10.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.88/10.14  % Solved by: fo/fo7.sh
% 9.88/10.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.88/10.14  % done 12410 iterations in 9.684s
% 9.88/10.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.88/10.14  % SZS output start Refutation
% 9.88/10.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.88/10.14  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 9.88/10.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.88/10.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.88/10.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.88/10.14  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 9.88/10.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.88/10.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.88/10.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.88/10.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.88/10.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.88/10.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.88/10.14  thf(sk_A_type, type, sk_A: $i).
% 9.88/10.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.88/10.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.88/10.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.88/10.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.88/10.15  thf(sk_C_type, type, sk_C: $i).
% 9.88/10.15  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.88/10.15  thf(sk_B_type, type, sk_B: $i).
% 9.88/10.15  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.88/10.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.88/10.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.88/10.15  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.88/10.15  thf(t76_funct_2, conjecture,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.88/10.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.88/10.15       ( ![C:$i]:
% 9.88/10.15         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.88/10.15             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.88/10.15           ( ( ( r2_relset_1 @
% 9.88/10.15                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 9.88/10.15               ( v2_funct_1 @ B ) ) =>
% 9.88/10.15             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 9.88/10.15  thf(zf_stmt_0, negated_conjecture,
% 9.88/10.15    (~( ![A:$i,B:$i]:
% 9.88/10.15        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.88/10.15            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.88/10.15          ( ![C:$i]:
% 9.88/10.15            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.88/10.15                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.88/10.15              ( ( ( r2_relset_1 @
% 9.88/10.15                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 9.88/10.15                  ( v2_funct_1 @ B ) ) =>
% 9.88/10.15                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 9.88/10.15    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 9.88/10.15  thf('0', plain,
% 9.88/10.15      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(redefinition_k6_partfun1, axiom,
% 9.88/10.15    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.88/10.15  thf('1', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.88/10.15  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['0', '1'])).
% 9.88/10.15  thf(t61_funct_1, axiom,
% 9.88/10.15    (![A:$i]:
% 9.88/10.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.88/10.15       ( ( v2_funct_1 @ A ) =>
% 9.88/10.15         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 9.88/10.15             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 9.88/10.15           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 9.88/10.15             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 9.88/10.15  thf('3', plain,
% 9.88/10.15      (![X14 : $i]:
% 9.88/10.15         (~ (v2_funct_1 @ X14)
% 9.88/10.15          | ((k5_relat_1 @ X14 @ (k2_funct_1 @ X14))
% 9.88/10.15              = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 9.88/10.15          | ~ (v1_funct_1 @ X14)
% 9.88/10.15          | ~ (v1_relat_1 @ X14))),
% 9.88/10.15      inference('cnf', [status(esa)], [t61_funct_1])).
% 9.88/10.15  thf('4', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(t67_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.88/10.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.88/10.15       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 9.88/10.15  thf('5', plain,
% 9.88/10.15      (![X63 : $i, X64 : $i]:
% 9.88/10.15         (((k1_relset_1 @ X63 @ X63 @ X64) = (X63))
% 9.88/10.15          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X63)))
% 9.88/10.15          | ~ (v1_funct_2 @ X64 @ X63 @ X63)
% 9.88/10.15          | ~ (v1_funct_1 @ X64))),
% 9.88/10.15      inference('cnf', [status(esa)], [t67_funct_2])).
% 9.88/10.15  thf('6', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.88/10.15        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['4', '5'])).
% 9.88/10.15  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('9', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(redefinition_k1_relset_1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.88/10.15       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.88/10.15  thf('10', plain,
% 9.88/10.15      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.88/10.15         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 9.88/10.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.88/10.15  thf('11', plain,
% 9.88/10.15      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['9', '10'])).
% 9.88/10.15  thf('12', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 9.88/10.15  thf(d10_xboole_0, axiom,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.88/10.15  thf('13', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.88/10.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.88/10.15  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.88/10.15      inference('simplify', [status(thm)], ['13'])).
% 9.88/10.15  thf(t4_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.88/10.15       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 9.88/10.15         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 9.88/10.15           ( m1_subset_1 @
% 9.88/10.15             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 9.88/10.15  thf('15', plain,
% 9.88/10.15      (![X61 : $i, X62 : $i]:
% 9.88/10.15         (~ (r1_tarski @ (k2_relat_1 @ X61) @ X62)
% 9.88/10.15          | (m1_subset_1 @ X61 @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X61) @ X62)))
% 9.88/10.15          | ~ (v1_funct_1 @ X61)
% 9.88/10.15          | ~ (v1_relat_1 @ X61))),
% 9.88/10.15      inference('cnf', [status(esa)], [t4_funct_2])).
% 9.88/10.15  thf('16', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_relat_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | (m1_subset_1 @ X0 @ 
% 9.88/10.15             (k1_zfmisc_1 @ 
% 9.88/10.15              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['14', '15'])).
% 9.88/10.15  thf('17', plain,
% 9.88/10.15      (((m1_subset_1 @ sk_B @ 
% 9.88/10.15         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 9.88/10.15        | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v1_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup+', [status(thm)], ['12', '16'])).
% 9.88/10.15  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('19', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(cc2_relat_1, axiom,
% 9.88/10.15    (![A:$i]:
% 9.88/10.15     ( ( v1_relat_1 @ A ) =>
% 9.88/10.15       ( ![B:$i]:
% 9.88/10.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.88/10.15  thf('20', plain,
% 9.88/10.15      (![X10 : $i, X11 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.88/10.15          | (v1_relat_1 @ X10)
% 9.88/10.15          | ~ (v1_relat_1 @ X11))),
% 9.88/10.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.88/10.15  thf('21', plain,
% 9.88/10.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['19', '20'])).
% 9.88/10.15  thf(fc6_relat_1, axiom,
% 9.88/10.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.88/10.15  thf('22', plain,
% 9.88/10.15      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 9.88/10.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.88/10.15  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 9.88/10.15      inference('demod', [status(thm)], ['21', '22'])).
% 9.88/10.15  thf('24', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 9.88/10.15      inference('demod', [status(thm)], ['17', '18', '23'])).
% 9.88/10.15  thf(t31_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.88/10.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.88/10.15       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 9.88/10.15         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 9.88/10.15           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 9.88/10.15           ( m1_subset_1 @
% 9.88/10.15             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 9.88/10.15  thf('25', plain,
% 9.88/10.15      (![X58 : $i, X59 : $i, X60 : $i]:
% 9.88/10.15         (~ (v2_funct_1 @ X58)
% 9.88/10.15          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 9.88/10.15          | (m1_subset_1 @ (k2_funct_1 @ X58) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 9.88/10.15          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 9.88/10.15          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 9.88/10.15          | ~ (v1_funct_1 @ X58))),
% 9.88/10.15      inference('cnf', [status(esa)], [t31_funct_2])).
% 9.88/10.15  thf('26', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.88/10.15        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.88/10.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 9.88/10.15        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.88/10.15            != (k2_relat_1 @ sk_B))
% 9.88/10.15        | ~ (v2_funct_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['24', '25'])).
% 9.88/10.15  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('28', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 9.88/10.15  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.88/10.15      inference('simplify', [status(thm)], ['13'])).
% 9.88/10.15  thf('30', plain,
% 9.88/10.15      (![X61 : $i, X62 : $i]:
% 9.88/10.15         (~ (r1_tarski @ (k2_relat_1 @ X61) @ X62)
% 9.88/10.15          | (v1_funct_2 @ X61 @ (k1_relat_1 @ X61) @ X62)
% 9.88/10.15          | ~ (v1_funct_1 @ X61)
% 9.88/10.15          | ~ (v1_relat_1 @ X61))),
% 9.88/10.15      inference('cnf', [status(esa)], [t4_funct_2])).
% 9.88/10.15  thf('31', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_relat_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['29', '30'])).
% 9.88/10.15  thf('32', plain,
% 9.88/10.15      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.88/10.15        | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v1_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup+', [status(thm)], ['28', '31'])).
% 9.88/10.15  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 9.88/10.15      inference('demod', [status(thm)], ['21', '22'])).
% 9.88/10.15  thf('35', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['32', '33', '34'])).
% 9.88/10.15  thf('36', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 9.88/10.15      inference('demod', [status(thm)], ['17', '18', '23'])).
% 9.88/10.15  thf(redefinition_k2_relset_1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.88/10.15       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.88/10.15  thf('37', plain,
% 9.88/10.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.88/10.15         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 9.88/10.15          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.88/10.15  thf('38', plain,
% 9.88/10.15      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['36', '37'])).
% 9.88/10.15  thf('39', plain, ((v2_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('40', plain,
% 9.88/10.15      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.88/10.15         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 9.88/10.15        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['26', '27', '35', '38', '39'])).
% 9.88/10.15  thf('41', plain,
% 9.88/10.15      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 9.88/10.15      inference('simplify', [status(thm)], ['40'])).
% 9.88/10.15  thf('42', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(dt_k1_partfun1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ E ) & 
% 9.88/10.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.88/10.15         ( v1_funct_1 @ F ) & 
% 9.88/10.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.88/10.15       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 9.88/10.15         ( m1_subset_1 @
% 9.88/10.15           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 9.88/10.15           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 9.88/10.15  thf('43', plain,
% 9.88/10.15      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.88/10.15          | ~ (v1_funct_1 @ X34)
% 9.88/10.15          | ~ (v1_funct_1 @ X37)
% 9.88/10.15          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.88/10.15          | (v1_funct_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)))),
% 9.88/10.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.88/10.15  thf('44', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['42', '43'])).
% 9.88/10.15  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('46', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0))),
% 9.88/10.15      inference('demod', [status(thm)], ['44', '45'])).
% 9.88/10.15  thf('47', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.88/10.15        | (v1_funct_1 @ 
% 9.88/10.15           (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 9.88/10.15            (k2_funct_1 @ sk_B))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['41', '46'])).
% 9.88/10.15  thf('48', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 9.88/10.15      inference('demod', [status(thm)], ['17', '18', '23'])).
% 9.88/10.15  thf('49', plain,
% 9.88/10.15      (![X58 : $i, X59 : $i, X60 : $i]:
% 9.88/10.15         (~ (v2_funct_1 @ X58)
% 9.88/10.15          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 9.88/10.15          | (v1_funct_1 @ (k2_funct_1 @ X58))
% 9.88/10.15          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 9.88/10.15          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 9.88/10.15          | ~ (v1_funct_1 @ X58))),
% 9.88/10.15      inference('cnf', [status(esa)], [t31_funct_2])).
% 9.88/10.15  thf('50', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.88/10.15        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.88/10.15        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.88/10.15            != (k2_relat_1 @ sk_B))
% 9.88/10.15        | ~ (v2_funct_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['48', '49'])).
% 9.88/10.15  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('52', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['32', '33', '34'])).
% 9.88/10.15  thf('53', plain, ((v2_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('54', plain,
% 9.88/10.15      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.88/10.15        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.88/10.15            != (k2_relat_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 9.88/10.15  thf('55', plain,
% 9.88/10.15      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['36', '37'])).
% 9.88/10.15  thf('56', plain,
% 9.88/10.15      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.88/10.15        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['54', '55'])).
% 9.88/10.15  thf('57', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 9.88/10.15      inference('simplify', [status(thm)], ['56'])).
% 9.88/10.15  thf('58', plain,
% 9.88/10.15      ((v1_funct_1 @ 
% 9.88/10.15        (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 9.88/10.15         (k2_funct_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['47', '57'])).
% 9.88/10.15  thf('59', plain,
% 9.88/10.15      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 9.88/10.15      inference('simplify', [status(thm)], ['40'])).
% 9.88/10.15  thf('60', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(redefinition_k1_partfun1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ E ) & 
% 9.88/10.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.88/10.15         ( v1_funct_1 @ F ) & 
% 9.88/10.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.88/10.15       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.88/10.15  thf('61', plain,
% 9.88/10.15      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 9.88/10.15          | ~ (v1_funct_1 @ X42)
% 9.88/10.15          | ~ (v1_funct_1 @ X45)
% 9.88/10.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 9.88/10.15          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 9.88/10.15              = (k5_relat_1 @ X42 @ X45)))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.88/10.15  thf('62', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 9.88/10.15            = (k5_relat_1 @ sk_B @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['60', '61'])).
% 9.88/10.15  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('64', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 9.88/10.15            = (k5_relat_1 @ sk_B @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0))),
% 9.88/10.15      inference('demod', [status(thm)], ['62', '63'])).
% 9.88/10.15  thf('65', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.88/10.15        | ((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 9.88/10.15            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['59', '64'])).
% 9.88/10.15  thf('66', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 9.88/10.15      inference('simplify', [status(thm)], ['56'])).
% 9.88/10.15  thf('67', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 9.88/10.15         (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['65', '66'])).
% 9.88/10.15  thf('68', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['58', '67'])).
% 9.88/10.15  thf('69', plain,
% 9.88/10.15      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 9.88/10.15        | ~ (v1_relat_1 @ sk_B)
% 9.88/10.15        | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ~ (v2_funct_1 @ sk_B))),
% 9.88/10.15      inference('sup+', [status(thm)], ['3', '68'])).
% 9.88/10.15  thf('70', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 9.88/10.15  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 9.88/10.15      inference('demod', [status(thm)], ['21', '22'])).
% 9.88/10.15  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('73', plain, ((v2_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('74', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 9.88/10.15  thf('75', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(dt_k6_partfun1, axiom,
% 9.88/10.15    (![A:$i]:
% 9.88/10.15     ( ( m1_subset_1 @
% 9.88/10.15         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 9.88/10.15       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 9.88/10.15  thf('76', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 9.88/10.15  thf('77', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.88/10.15  thf('78', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf('79', plain,
% 9.88/10.15      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 9.88/10.15          | ~ (v1_funct_1 @ X42)
% 9.88/10.15          | ~ (v1_funct_1 @ X45)
% 9.88/10.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 9.88/10.15          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 9.88/10.15              = (k5_relat_1 @ X42 @ X45)))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.88/10.15  thf('80', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.88/10.15         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 9.88/10.15            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.88/10.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.88/10.15          | ~ (v1_funct_1 @ X1)
% 9.88/10.15          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['78', '79'])).
% 9.88/10.15  thf('81', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.88/10.15          | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.88/10.15              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['75', '80'])).
% 9.88/10.15  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('83', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.88/10.15          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.88/10.15              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 9.88/10.15      inference('demod', [status(thm)], ['81', '82'])).
% 9.88/10.15  thf('84', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.88/10.15         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['74', '83'])).
% 9.88/10.15  thf('85', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(t23_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.88/10.15       ( ( r2_relset_1 @
% 9.88/10.15           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 9.88/10.15           C ) & 
% 9.88/10.15         ( r2_relset_1 @
% 9.88/10.15           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 9.88/10.15           C ) ) ))).
% 9.88/10.15  thf('86', plain,
% 9.88/10.15      (![X49 : $i, X50 : $i, X51 : $i]:
% 9.88/10.15         ((r2_relset_1 @ X49 @ X50 @ 
% 9.88/10.15           (k4_relset_1 @ X49 @ X49 @ X49 @ X50 @ (k6_partfun1 @ X49) @ X51) @ 
% 9.88/10.15           X51)
% 9.88/10.15          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 9.88/10.15      inference('cnf', [status(esa)], [t23_funct_2])).
% 9.88/10.15  thf('87', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.88/10.15  thf('88', plain,
% 9.88/10.15      (![X49 : $i, X50 : $i, X51 : $i]:
% 9.88/10.15         ((r2_relset_1 @ X49 @ X50 @ 
% 9.88/10.15           (k4_relset_1 @ X49 @ X49 @ X49 @ X50 @ (k6_relat_1 @ X49) @ X51) @ 
% 9.88/10.15           X51)
% 9.88/10.15          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 9.88/10.15      inference('demod', [status(thm)], ['86', '87'])).
% 9.88/10.15  thf('89', plain,
% 9.88/10.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.88/10.15        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.88/10.15        sk_B)),
% 9.88/10.15      inference('sup-', [status(thm)], ['85', '88'])).
% 9.88/10.15  thf('90', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('91', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf(redefinition_k4_relset_1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.88/10.15     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.88/10.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.88/10.15       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.88/10.15  thf('92', plain,
% 9.88/10.15      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 9.88/10.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.88/10.15          | ((k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 9.88/10.15              = (k5_relat_1 @ X21 @ X24)))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 9.88/10.15  thf('93', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.88/10.15         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 9.88/10.15            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.88/10.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['91', '92'])).
% 9.88/10.15  thf('94', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.88/10.15           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['90', '93'])).
% 9.88/10.15  thf('95', plain,
% 9.88/10.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.88/10.15        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 9.88/10.15      inference('demod', [status(thm)], ['89', '94'])).
% 9.88/10.15  thf('96', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 9.88/10.15  thf('97', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('98', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf('99', plain,
% 9.88/10.15      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.88/10.15          | ~ (v1_funct_1 @ X34)
% 9.88/10.15          | ~ (v1_funct_1 @ X37)
% 9.88/10.15          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.88/10.15          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 9.88/10.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.88/10.15  thf('100', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.88/10.15         ((m1_subset_1 @ 
% 9.88/10.15           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 9.88/10.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 9.88/10.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X2)
% 9.88/10.15          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['98', '99'])).
% 9.88/10.15  thf('101', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.88/10.15          | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15          | (m1_subset_1 @ 
% 9.88/10.15             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['97', '100'])).
% 9.88/10.15  thf('102', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('103', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.88/10.15          | (m1_subset_1 @ 
% 9.88/10.15             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 9.88/10.15      inference('demod', [status(thm)], ['101', '102'])).
% 9.88/10.15  thf('104', plain,
% 9.88/10.15      ((m1_subset_1 @ 
% 9.88/10.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['96', '103'])).
% 9.88/10.15  thf('105', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.88/10.15         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 9.88/10.15      inference('sup-', [status(thm)], ['74', '83'])).
% 9.88/10.15  thf('106', plain,
% 9.88/10.15      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('demod', [status(thm)], ['104', '105'])).
% 9.88/10.15  thf(redefinition_r2_relset_1, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i,D:$i]:
% 9.88/10.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.88/10.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.88/10.15       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.88/10.15  thf('107', plain,
% 9.88/10.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | ((X27) = (X30))
% 9.88/10.15          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.88/10.15  thf('108', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.88/10.15             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 9.88/10.15          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['106', '107'])).
% 9.88/10.15  thf('109', plain,
% 9.88/10.15      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['95', '108'])).
% 9.88/10.15  thf('110', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('111', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['109', '110'])).
% 9.88/10.15  thf('112', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.88/10.15         = (sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['84', '111'])).
% 9.88/10.15  thf('113', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('114', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('115', plain,
% 9.88/10.15      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 9.88/10.15          | ~ (v1_funct_1 @ X42)
% 9.88/10.15          | ~ (v1_funct_1 @ X45)
% 9.88/10.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 9.88/10.15          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 9.88/10.15              = (k5_relat_1 @ X42 @ X45)))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.88/10.15  thf('116', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 9.88/10.15            = (k5_relat_1 @ sk_C @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_C))),
% 9.88/10.15      inference('sup-', [status(thm)], ['114', '115'])).
% 9.88/10.15  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('118', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 9.88/10.15            = (k5_relat_1 @ sk_C @ X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.88/10.15          | ~ (v1_funct_1 @ X0))),
% 9.88/10.15      inference('demod', [status(thm)], ['116', '117'])).
% 9.88/10.15  thf('119', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.88/10.15            = (k5_relat_1 @ sk_C @ sk_B)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['113', '118'])).
% 9.88/10.15  thf('120', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('121', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.88/10.15         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['119', '120'])).
% 9.88/10.15  thf('122', plain,
% 9.88/10.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.88/10.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('123', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.88/10.15         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['119', '120'])).
% 9.88/10.15  thf('124', plain,
% 9.88/10.15      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 9.88/10.15      inference('demod', [status(thm)], ['122', '123'])).
% 9.88/10.15  thf('125', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('126', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('127', plain,
% 9.88/10.15      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.88/10.15          | ~ (v1_funct_1 @ X34)
% 9.88/10.15          | ~ (v1_funct_1 @ X37)
% 9.88/10.15          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.88/10.15          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 9.88/10.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.88/10.15  thf('128', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 9.88/10.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.88/10.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.88/10.15          | ~ (v1_funct_1 @ X1)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_C))),
% 9.88/10.15      inference('sup-', [status(thm)], ['126', '127'])).
% 9.88/10.15  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('130', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 9.88/10.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.88/10.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.88/10.15          | ~ (v1_funct_1 @ X1))),
% 9.88/10.15      inference('demod', [status(thm)], ['128', '129'])).
% 9.88/10.15  thf('131', plain,
% 9.88/10.15      ((~ (v1_funct_1 @ sk_B)
% 9.88/10.15        | (m1_subset_1 @ 
% 9.88/10.15           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 9.88/10.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['125', '130'])).
% 9.88/10.15  thf('132', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('133', plain,
% 9.88/10.15      ((m1_subset_1 @ 
% 9.88/10.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('demod', [status(thm)], ['131', '132'])).
% 9.88/10.15  thf('134', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.88/10.15         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['119', '120'])).
% 9.88/10.15  thf('135', plain,
% 9.88/10.15      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 9.88/10.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('demod', [status(thm)], ['133', '134'])).
% 9.88/10.15  thf('136', plain,
% 9.88/10.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | ((X27) = (X30))
% 9.88/10.15          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.88/10.15  thf('137', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 9.88/10.15          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.88/10.15      inference('sup-', [status(thm)], ['135', '136'])).
% 9.88/10.15  thf('138', plain,
% 9.88/10.15      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['124', '137'])).
% 9.88/10.15  thf('139', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('140', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['138', '139'])).
% 9.88/10.15  thf('141', plain,
% 9.88/10.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 9.88/10.15      inference('demod', [status(thm)], ['121', '140'])).
% 9.88/10.15  thf('142', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf(t27_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.88/10.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.88/10.15       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 9.88/10.15            ( ~( ( v2_funct_1 @ C ) <=>
% 9.88/10.15                 ( ![D:$i,E:$i]:
% 9.88/10.15                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 9.88/10.15                       ( m1_subset_1 @
% 9.88/10.15                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 9.88/10.15                     ( ![F:$i]:
% 9.88/10.15                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 9.88/10.15                           ( m1_subset_1 @
% 9.88/10.15                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 9.88/10.15                         ( ( r2_relset_1 @
% 9.88/10.15                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 9.88/10.15                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 9.88/10.15                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 9.88/10.15  thf('143', plain,
% 9.88/10.15      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 9.88/10.15         (((X52) = (k1_xboole_0))
% 9.88/10.15          | ((X53) = (k1_xboole_0))
% 9.88/10.15          | ~ (v1_funct_1 @ X54)
% 9.88/10.15          | ~ (v1_funct_2 @ X54 @ X53 @ X52)
% 9.88/10.15          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 9.88/10.15          | ~ (v1_funct_1 @ X55)
% 9.88/10.15          | ~ (v1_funct_2 @ X55 @ X56 @ X53)
% 9.88/10.15          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X53)))
% 9.88/10.15          | ~ (r2_relset_1 @ X56 @ X52 @ 
% 9.88/10.15               (k1_partfun1 @ X56 @ X53 @ X53 @ X52 @ X55 @ X54) @ 
% 9.88/10.15               (k1_partfun1 @ X56 @ X53 @ X53 @ X52 @ X57 @ X54))
% 9.88/10.15          | (r2_relset_1 @ X56 @ X53 @ X55 @ X57)
% 9.88/10.15          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X53)))
% 9.88/10.15          | ~ (v1_funct_2 @ X57 @ X56 @ X53)
% 9.88/10.15          | ~ (v1_funct_1 @ X57)
% 9.88/10.15          | ~ (v2_funct_1 @ X54))),
% 9.88/10.15      inference('cnf', [status(esa)], [t27_funct_2])).
% 9.88/10.15  thf('144', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (~ (v2_funct_1 @ sk_B)
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.88/10.15          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.88/10.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.88/10.15          | ~ (v1_funct_1 @ X2)
% 9.88/10.15          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_B)
% 9.88/10.15          | ((sk_A) = (k1_xboole_0))
% 9.88/10.15          | ((sk_A) = (k1_xboole_0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['142', '143'])).
% 9.88/10.15  thf('145', plain, ((v2_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('146', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('147', plain, ((v1_funct_1 @ sk_B)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('148', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.88/10.15          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.88/10.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.88/10.15          | ~ (v1_funct_1 @ X2)
% 9.88/10.15          | ((sk_A) = (k1_xboole_0))
% 9.88/10.15          | ((sk_A) = (k1_xboole_0)))),
% 9.88/10.15      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 9.88/10.15  thf('149', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.88/10.15         (((sk_A) = (k1_xboole_0))
% 9.88/10.15          | ~ (v1_funct_1 @ X2)
% 9.88/10.15          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.88/10.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.88/10.15               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.88/10.15          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.88/10.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.88/10.15          | ~ (v1_funct_1 @ X0))),
% 9.88/10.15      inference('simplify', [status(thm)], ['148'])).
% 9.88/10.15  thf('150', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 9.88/10.15             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 9.88/10.15          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 9.88/10.15          | ~ (v1_funct_1 @ sk_C)
% 9.88/10.15          | ((sk_A) = (k1_xboole_0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['141', '149'])).
% 9.88/10.15  thf('151', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('152', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('154', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 9.88/10.15             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.88/10.15          | ~ (v1_funct_1 @ X0)
% 9.88/10.15          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.88/10.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 9.88/10.15          | ((sk_A) = (k1_xboole_0)))),
% 9.88/10.15      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 9.88/10.15  thf('155', plain,
% 9.88/10.15      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 9.88/10.15        | ((sk_A) = (k1_xboole_0))
% 9.88/10.15        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 9.88/10.15        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 9.88/10.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.88/10.15        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 9.88/10.15        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['112', '154'])).
% 9.88/10.15  thf('156', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('157', plain,
% 9.88/10.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 9.88/10.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 9.88/10.15          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 9.88/10.15          | ((X27) != (X30)))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.88/10.15  thf('158', plain,
% 9.88/10.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.88/10.15         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 9.88/10.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 9.88/10.15      inference('simplify', [status(thm)], ['157'])).
% 9.88/10.15  thf('159', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 9.88/10.15      inference('sup-', [status(thm)], ['156', '158'])).
% 9.88/10.15  thf('160', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf('161', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 9.88/10.15  thf('162', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf(cc1_funct_2, axiom,
% 9.88/10.15    (![A:$i,B:$i,C:$i]:
% 9.88/10.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.88/10.15       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 9.88/10.15         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 9.88/10.15  thf('163', plain,
% 9.88/10.15      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.88/10.15         (~ (v1_funct_1 @ X31)
% 9.88/10.15          | ~ (v1_partfun1 @ X31 @ X32)
% 9.88/10.15          | (v1_funct_2 @ X31 @ X32 @ X33)
% 9.88/10.15          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 9.88/10.15      inference('cnf', [status(esa)], [cc1_funct_2])).
% 9.88/10.15  thf('164', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 9.88/10.15          | ~ (v1_partfun1 @ (k6_relat_1 @ X0) @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['162', '163'])).
% 9.88/10.15  thf('165', plain, (![X40 : $i]: (v1_partfun1 @ (k6_partfun1 @ X40) @ X40)),
% 9.88/10.15      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 9.88/10.15  thf('166', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 9.88/10.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.88/10.15  thf('167', plain, (![X40 : $i]: (v1_partfun1 @ (k6_relat_1 @ X40) @ X40)),
% 9.88/10.15      inference('demod', [status(thm)], ['165', '166'])).
% 9.88/10.15  thf('168', plain,
% 9.88/10.15      (![X0 : $i]:
% 9.88/10.15         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 9.88/10.15          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.88/10.15      inference('demod', [status(thm)], ['164', '167'])).
% 9.88/10.15  thf('169', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 9.88/10.15      inference('sup-', [status(thm)], ['161', '168'])).
% 9.88/10.15  thf('170', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 9.88/10.15  thf('171', plain,
% 9.88/10.15      ((((sk_A) = (k1_xboole_0))
% 9.88/10.15        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 9.88/10.15      inference('demod', [status(thm)], ['155', '159', '160', '169', '170'])).
% 9.88/10.15  thf('172', plain,
% 9.88/10.15      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 9.88/10.15      inference('demod', [status(thm)], ['0', '1'])).
% 9.88/10.15  thf('173', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('174', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('175', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf(t113_zfmisc_1, axiom,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.88/10.15       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.88/10.15  thf('176', plain,
% 9.88/10.15      (![X5 : $i, X6 : $i]:
% 9.88/10.15         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 9.88/10.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.88/10.15  thf('177', plain,
% 9.88/10.15      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 9.88/10.15      inference('simplify', [status(thm)], ['176'])).
% 9.88/10.15  thf('178', plain,
% 9.88/10.15      (![X41 : $i]:
% 9.88/10.15         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 9.88/10.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 9.88/10.15      inference('demod', [status(thm)], ['76', '77'])).
% 9.88/10.15  thf('179', plain,
% 9.88/10.15      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 9.88/10.15      inference('sup+', [status(thm)], ['177', '178'])).
% 9.88/10.15  thf(t3_subset, axiom,
% 9.88/10.15    (![A:$i,B:$i]:
% 9.88/10.15     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.88/10.15  thf('180', plain,
% 9.88/10.15      (![X7 : $i, X8 : $i]:
% 9.88/10.15         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 9.88/10.15      inference('cnf', [status(esa)], [t3_subset])).
% 9.88/10.15  thf('181', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 9.88/10.15      inference('sup-', [status(thm)], ['179', '180'])).
% 9.88/10.15  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.88/10.15  thf('182', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.88/10.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.88/10.15  thf('183', plain,
% 9.88/10.15      (![X0 : $i, X2 : $i]:
% 9.88/10.15         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.88/10.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.88/10.15  thf('184', plain,
% 9.88/10.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['182', '183'])).
% 9.88/10.15  thf('185', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.88/10.15      inference('sup-', [status(thm)], ['181', '184'])).
% 9.88/10.15  thf('186', plain,
% 9.88/10.15      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 9.88/10.15      inference('demod', [status(thm)], ['2', '173', '174', '175', '185'])).
% 9.88/10.15  thf('187', plain,
% 9.88/10.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.88/10.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.88/10.15  thf('188', plain,
% 9.88/10.15      (![X7 : $i, X8 : $i]:
% 9.88/10.15         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 9.88/10.15      inference('cnf', [status(esa)], [t3_subset])).
% 9.88/10.15  thf('189', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 9.88/10.15      inference('sup-', [status(thm)], ['187', '188'])).
% 9.88/10.15  thf('190', plain,
% 9.88/10.15      (![X0 : $i, X2 : $i]:
% 9.88/10.15         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.88/10.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.88/10.15  thf('191', plain,
% 9.88/10.15      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 9.88/10.15        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 9.88/10.15      inference('sup-', [status(thm)], ['189', '190'])).
% 9.88/10.15  thf('192', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('193', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('194', plain,
% 9.88/10.15      (![X5 : $i, X6 : $i]:
% 9.88/10.15         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 9.88/10.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.88/10.15  thf('195', plain,
% 9.88/10.15      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 9.88/10.15      inference('simplify', [status(thm)], ['194'])).
% 9.88/10.15  thf('196', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.88/10.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.88/10.15  thf('197', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('198', plain, (((sk_A) = (k1_xboole_0))),
% 9.88/10.15      inference('clc', [status(thm)], ['171', '172'])).
% 9.88/10.15  thf('199', plain,
% 9.88/10.15      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 9.88/10.15      inference('simplify', [status(thm)], ['194'])).
% 9.88/10.15  thf('200', plain, (((k1_xboole_0) = (sk_C))),
% 9.88/10.15      inference('demod', [status(thm)],
% 9.88/10.15                ['191', '192', '193', '195', '196', '197', '198', '199'])).
% 9.88/10.15  thf('201', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 9.88/10.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.88/10.15  thf('202', plain,
% 9.88/10.15      (![X7 : $i, X9 : $i]:
% 9.88/10.15         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 9.88/10.15      inference('cnf', [status(esa)], [t3_subset])).
% 9.88/10.15  thf('203', plain,
% 9.88/10.15      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.88/10.15      inference('sup-', [status(thm)], ['201', '202'])).
% 9.88/10.15  thf('204', plain,
% 9.88/10.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.88/10.15         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 9.88/10.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 9.88/10.15      inference('simplify', [status(thm)], ['157'])).
% 9.88/10.15  thf('205', plain,
% 9.88/10.15      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 9.88/10.15      inference('sup-', [status(thm)], ['203', '204'])).
% 9.88/10.15  thf('206', plain, ($false),
% 9.88/10.15      inference('demod', [status(thm)], ['186', '200', '205'])).
% 9.88/10.15  
% 9.88/10.15  % SZS output end Refutation
% 9.88/10.15  
% 9.88/10.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
