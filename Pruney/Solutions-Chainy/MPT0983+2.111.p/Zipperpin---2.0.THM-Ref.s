%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f4wkOGzQH6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:18 EST 2020

% Result     : Theorem 5.59s
% Output     : Refutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 339 expanded)
%              Number of leaves         :   50 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          : 1283 (5338 expanded)
%              Number of equality atoms :   44 (  81 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('8',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X33 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X34: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('22',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X34: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X34 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('39',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('40',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('44',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58 ) )
      | ( v2_funct_1 @ X62 )
      | ( X60 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X61 @ X59 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X34: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X34 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('65',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','69'])).

thf('71',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('76',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('83',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('84',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('85',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('92',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('101',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','99','100','101','102','107'])).

thf('109',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('112',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k2_relat_1 @ X44 )
       != X43 )
      | ( v2_funct_2 @ X44 @ X43 )
      | ~ ( v5_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('113',plain,(
    ! [X44: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v5_relat_1 @ X44 @ ( k2_relat_1 @ X44 ) )
      | ( v2_funct_2 @ X44 @ ( k2_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['96','97'])).

thf('118',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['73','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f4wkOGzQH6
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.59/5.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.59/5.81  % Solved by: fo/fo7.sh
% 5.59/5.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.59/5.81  % done 5647 iterations in 5.349s
% 5.59/5.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.59/5.81  % SZS output start Refutation
% 5.59/5.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.59/5.81  thf(sk_A_type, type, sk_A: $i).
% 5.59/5.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.59/5.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.59/5.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.59/5.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.59/5.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.59/5.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.59/5.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.59/5.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.59/5.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.59/5.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.59/5.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.59/5.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.59/5.81  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.59/5.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.59/5.81  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.59/5.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.59/5.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.59/5.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.59/5.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.59/5.81  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.59/5.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.59/5.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.59/5.81  thf(sk_D_type, type, sk_D: $i).
% 5.59/5.81  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.59/5.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.59/5.81  thf(t29_funct_2, conjecture,
% 5.59/5.81    (![A:$i,B:$i,C:$i]:
% 5.59/5.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.59/5.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.59/5.81       ( ![D:$i]:
% 5.59/5.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.59/5.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.59/5.81           ( ( r2_relset_1 @
% 5.59/5.81               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.59/5.81               ( k6_partfun1 @ A ) ) =>
% 5.59/5.81             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.59/5.81  thf(zf_stmt_0, negated_conjecture,
% 5.59/5.81    (~( ![A:$i,B:$i,C:$i]:
% 5.59/5.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.59/5.81            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.59/5.81          ( ![D:$i]:
% 5.59/5.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.59/5.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.59/5.81              ( ( r2_relset_1 @
% 5.59/5.81                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.59/5.81                  ( k6_partfun1 @ A ) ) =>
% 5.59/5.81                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.59/5.81    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.59/5.81  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('1', plain,
% 5.59/5.81      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.59/5.81      inference('split', [status(esa)], ['0'])).
% 5.59/5.81  thf(t71_relat_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.59/5.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.59/5.81  thf('2', plain, (![X32 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 5.59/5.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.59/5.81  thf(redefinition_k6_partfun1, axiom,
% 5.59/5.81    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.59/5.81  thf('3', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.59/5.81  thf('4', plain, (![X32 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X32)) = (X32))),
% 5.59/5.81      inference('demod', [status(thm)], ['2', '3'])).
% 5.59/5.81  thf(fc9_relat_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 5.59/5.81       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 5.59/5.81  thf('5', plain,
% 5.59/5.81      (![X28 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ (k2_relat_1 @ X28))
% 5.59/5.81          | ~ (v1_relat_1 @ X28)
% 5.59/5.81          | (v1_xboole_0 @ X28))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc9_relat_1])).
% 5.59/5.81  thf('6', plain,
% 5.59/5.81      (![X0 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ X0)
% 5.59/5.81          | (v1_xboole_0 @ (k6_partfun1 @ X0))
% 5.59/5.81          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['4', '5'])).
% 5.59/5.81  thf(fc4_funct_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.59/5.81       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.59/5.81  thf('7', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.59/5.81  thf('8', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.59/5.81  thf('9', plain, (![X33 : $i]: (v1_relat_1 @ (k6_partfun1 @ X33))),
% 5.59/5.81      inference('demod', [status(thm)], ['7', '8'])).
% 5.59/5.81  thf('10', plain,
% 5.59/5.81      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 5.59/5.81      inference('demod', [status(thm)], ['6', '9'])).
% 5.59/5.81  thf(d3_tarski, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( r1_tarski @ A @ B ) <=>
% 5.59/5.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.59/5.81  thf('11', plain,
% 5.59/5.81      (![X4 : $i, X6 : $i]:
% 5.59/5.81         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 5.59/5.81      inference('cnf', [status(esa)], [d3_tarski])).
% 5.59/5.81  thf(d1_xboole_0, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.59/5.81  thf('12', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.59/5.81      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.59/5.81  thf('13', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 5.59/5.81      inference('sup-', [status(thm)], ['11', '12'])).
% 5.59/5.81  thf('14', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 5.59/5.81      inference('sup-', [status(thm)], ['11', '12'])).
% 5.59/5.81  thf(d10_xboole_0, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.59/5.81  thf('15', plain,
% 5.59/5.81      (![X7 : $i, X9 : $i]:
% 5.59/5.81         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 5.59/5.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.59/5.81  thf('16', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['14', '15'])).
% 5.59/5.81  thf('17', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.59/5.81      inference('sup-', [status(thm)], ['13', '16'])).
% 5.59/5.81  thf('18', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ X0)
% 5.59/5.81          | ~ (v1_xboole_0 @ X1)
% 5.59/5.81          | ((k6_partfun1 @ X0) = (X1)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['10', '17'])).
% 5.59/5.81  thf('19', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('split', [status(esa)], ['0'])).
% 5.59/5.81  thf('20', plain,
% 5.59/5.81      ((![X0 : $i]:
% 5.59/5.81          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.59/5.81           | ~ (v1_xboole_0 @ sk_C_1)
% 5.59/5.81           | ~ (v1_xboole_0 @ X0)))
% 5.59/5.81         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['18', '19'])).
% 5.59/5.81  thf('21', plain, (![X34 : $i]: (v2_funct_1 @ (k6_relat_1 @ X34))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.59/5.81  thf('22', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.59/5.81  thf('23', plain, (![X34 : $i]: (v2_funct_1 @ (k6_partfun1 @ X34))),
% 5.59/5.81      inference('demod', [status(thm)], ['21', '22'])).
% 5.59/5.81  thf('24', plain,
% 5.59/5.81      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 5.59/5.81         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('demod', [status(thm)], ['20', '23'])).
% 5.59/5.81  thf('25', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('condensation', [status(thm)], ['24'])).
% 5.59/5.81  thf('26', plain,
% 5.59/5.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.59/5.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.59/5.81        (k6_partfun1 @ sk_A))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('27', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('28', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(dt_k1_partfun1, axiom,
% 5.59/5.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.59/5.81     ( ( ( v1_funct_1 @ E ) & 
% 5.59/5.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.59/5.81         ( v1_funct_1 @ F ) & 
% 5.59/5.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.59/5.81       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.59/5.81         ( m1_subset_1 @
% 5.59/5.81           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.59/5.81           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.59/5.81  thf('29', plain,
% 5.59/5.81      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 5.59/5.81          | ~ (v1_funct_1 @ X45)
% 5.59/5.81          | ~ (v1_funct_1 @ X48)
% 5.59/5.81          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 5.59/5.81          | (m1_subset_1 @ (k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48) @ 
% 5.59/5.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X50))))),
% 5.59/5.81      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.59/5.81  thf('30', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.59/5.81         ((m1_subset_1 @ 
% 5.59/5.81           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.59/5.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.59/5.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.59/5.81          | ~ (v1_funct_1 @ X1)
% 5.59/5.81          | ~ (v1_funct_1 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['28', '29'])).
% 5.59/5.81  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('32', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.59/5.81         ((m1_subset_1 @ 
% 5.59/5.81           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.59/5.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.59/5.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.59/5.81          | ~ (v1_funct_1 @ X1))),
% 5.59/5.81      inference('demod', [status(thm)], ['30', '31'])).
% 5.59/5.81  thf('33', plain,
% 5.59/5.81      ((~ (v1_funct_1 @ sk_D)
% 5.59/5.81        | (m1_subset_1 @ 
% 5.59/5.81           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.59/5.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.59/5.81      inference('sup-', [status(thm)], ['27', '32'])).
% 5.59/5.81  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('35', plain,
% 5.59/5.81      ((m1_subset_1 @ 
% 5.59/5.81        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.59/5.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.59/5.81      inference('demod', [status(thm)], ['33', '34'])).
% 5.59/5.81  thf(redefinition_r2_relset_1, axiom,
% 5.59/5.81    (![A:$i,B:$i,C:$i,D:$i]:
% 5.59/5.81     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.59/5.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.59/5.81       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.59/5.81  thf('36', plain,
% 5.59/5.81      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.59/5.81          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.59/5.81          | ((X38) = (X41))
% 5.59/5.81          | ~ (r2_relset_1 @ X39 @ X40 @ X38 @ X41))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.59/5.81  thf('37', plain,
% 5.59/5.81      (![X0 : $i]:
% 5.59/5.81         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.59/5.81             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 5.59/5.81          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.59/5.81              = (X0))
% 5.59/5.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.59/5.81      inference('sup-', [status(thm)], ['35', '36'])).
% 5.59/5.81  thf('38', plain,
% 5.59/5.81      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.59/5.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.59/5.81        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.59/5.81            = (k6_partfun1 @ sk_A)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['26', '37'])).
% 5.59/5.81  thf(t29_relset_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( m1_subset_1 @
% 5.59/5.81       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.59/5.81  thf('39', plain,
% 5.59/5.81      (![X42 : $i]:
% 5.59/5.81         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 5.59/5.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 5.59/5.81      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.59/5.81  thf('40', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.59/5.81  thf('41', plain,
% 5.59/5.81      (![X42 : $i]:
% 5.59/5.81         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 5.59/5.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 5.59/5.81      inference('demod', [status(thm)], ['39', '40'])).
% 5.59/5.81  thf('42', plain,
% 5.59/5.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.59/5.81         = (k6_partfun1 @ sk_A))),
% 5.59/5.81      inference('demod', [status(thm)], ['38', '41'])).
% 5.59/5.81  thf('43', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(t26_funct_2, axiom,
% 5.59/5.81    (![A:$i,B:$i,C:$i,D:$i]:
% 5.59/5.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.59/5.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.59/5.81       ( ![E:$i]:
% 5.59/5.81         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.59/5.81             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.59/5.81           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.59/5.81             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.59/5.81               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.59/5.81  thf('44', plain,
% 5.59/5.81      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 5.59/5.81         (~ (v1_funct_1 @ X58)
% 5.59/5.81          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 5.59/5.81          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 5.59/5.81          | ~ (v2_funct_1 @ (k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58))
% 5.59/5.81          | (v2_funct_1 @ X62)
% 5.59/5.81          | ((X60) = (k1_xboole_0))
% 5.59/5.81          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 5.59/5.81          | ~ (v1_funct_2 @ X62 @ X61 @ X59)
% 5.59/5.81          | ~ (v1_funct_1 @ X62))),
% 5.59/5.81      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.59/5.81  thf('45', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_funct_1 @ X0)
% 5.59/5.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.59/5.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.59/5.81          | ((sk_A) = (k1_xboole_0))
% 5.59/5.81          | (v2_funct_1 @ X0)
% 5.59/5.81          | ~ (v2_funct_1 @ 
% 5.59/5.81               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 5.59/5.81          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.59/5.81          | ~ (v1_funct_1 @ sk_D))),
% 5.59/5.81      inference('sup-', [status(thm)], ['43', '44'])).
% 5.59/5.81  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('48', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_funct_1 @ X0)
% 5.59/5.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.59/5.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.59/5.81          | ((sk_A) = (k1_xboole_0))
% 5.59/5.81          | (v2_funct_1 @ X0)
% 5.59/5.81          | ~ (v2_funct_1 @ 
% 5.59/5.81               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 5.59/5.81      inference('demod', [status(thm)], ['45', '46', '47'])).
% 5.59/5.81  thf('49', plain,
% 5.59/5.81      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 5.59/5.81        | (v2_funct_1 @ sk_C_1)
% 5.59/5.81        | ((sk_A) = (k1_xboole_0))
% 5.59/5.81        | ~ (m1_subset_1 @ sk_C_1 @ 
% 5.59/5.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 5.59/5.81        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 5.59/5.81        | ~ (v1_funct_1 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['42', '48'])).
% 5.59/5.81  thf('50', plain, (![X34 : $i]: (v2_funct_1 @ (k6_partfun1 @ X34))),
% 5.59/5.81      inference('demod', [status(thm)], ['21', '22'])).
% 5.59/5.81  thf('51', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('52', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('54', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 5.59/5.81      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 5.59/5.81  thf('55', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('split', [status(esa)], ['0'])).
% 5.59/5.81  thf('56', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['54', '55'])).
% 5.59/5.81  thf(fc4_zfmisc_1, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 5.59/5.81  thf('57', plain,
% 5.59/5.81      (![X15 : $i, X16 : $i]:
% 5.59/5.81         (~ (v1_xboole_0 @ X15) | (v1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 5.59/5.81  thf('58', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(cc1_subset_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( v1_xboole_0 @ A ) =>
% 5.59/5.81       ( ![B:$i]:
% 5.59/5.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 5.59/5.81  thf('59', plain,
% 5.59/5.81      (![X17 : $i, X18 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 5.59/5.81          | (v1_xboole_0 @ X17)
% 5.59/5.81          | ~ (v1_xboole_0 @ X18))),
% 5.59/5.81      inference('cnf', [status(esa)], [cc1_subset_1])).
% 5.59/5.81  thf('60', plain,
% 5.59/5.81      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 5.59/5.81        | (v1_xboole_0 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['58', '59'])).
% 5.59/5.81  thf('61', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['57', '60'])).
% 5.59/5.81  thf('62', plain,
% 5.59/5.81      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1)))
% 5.59/5.81         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['56', '61'])).
% 5.59/5.81  thf('63', plain,
% 5.59/5.81      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 5.59/5.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.59/5.81  thf('64', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 5.59/5.81      inference('simplify', [status(thm)], ['63'])).
% 5.59/5.81  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 5.59/5.81  thf('65', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 5.59/5.81      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.59/5.81  thf(t69_xboole_1, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( ~( v1_xboole_0 @ B ) ) =>
% 5.59/5.81       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 5.59/5.81  thf('66', plain,
% 5.59/5.81      (![X11 : $i, X12 : $i]:
% 5.59/5.81         (~ (r1_xboole_0 @ X11 @ X12)
% 5.59/5.81          | ~ (r1_tarski @ X11 @ X12)
% 5.59/5.81          | (v1_xboole_0 @ X11))),
% 5.59/5.81      inference('cnf', [status(esa)], [t69_xboole_1])).
% 5.59/5.81  thf('67', plain,
% 5.59/5.81      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 5.59/5.81      inference('sup-', [status(thm)], ['65', '66'])).
% 5.59/5.81  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.59/5.81      inference('sup-', [status(thm)], ['64', '67'])).
% 5.59/5.81  thf('69', plain, (((v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.59/5.81      inference('demod', [status(thm)], ['62', '68'])).
% 5.59/5.81  thf('70', plain, (((v2_funct_1 @ sk_C_1))),
% 5.59/5.81      inference('demod', [status(thm)], ['25', '69'])).
% 5.59/5.81  thf('71', plain,
% 5.59/5.81      (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C_1))),
% 5.59/5.81      inference('split', [status(esa)], ['0'])).
% 5.59/5.81  thf('72', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.59/5.81      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 5.59/5.81  thf('73', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 5.59/5.81      inference('simpl_trail', [status(thm)], ['1', '72'])).
% 5.59/5.81  thf('74', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('75', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(redefinition_k1_partfun1, axiom,
% 5.59/5.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.59/5.81     ( ( ( v1_funct_1 @ E ) & 
% 5.59/5.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.59/5.81         ( v1_funct_1 @ F ) & 
% 5.59/5.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.59/5.81       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.59/5.81  thf('76', plain,
% 5.59/5.81      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 5.59/5.81          | ~ (v1_funct_1 @ X51)
% 5.59/5.81          | ~ (v1_funct_1 @ X54)
% 5.59/5.81          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 5.59/5.81          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 5.59/5.81              = (k5_relat_1 @ X51 @ X54)))),
% 5.59/5.81      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.59/5.81  thf('77', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.59/5.81         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 5.59/5.81            = (k5_relat_1 @ sk_C_1 @ X0))
% 5.59/5.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.59/5.81          | ~ (v1_funct_1 @ X0)
% 5.59/5.81          | ~ (v1_funct_1 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['75', '76'])).
% 5.59/5.81  thf('78', plain, ((v1_funct_1 @ sk_C_1)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('79', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.59/5.81         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 5.59/5.81            = (k5_relat_1 @ sk_C_1 @ X0))
% 5.59/5.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.59/5.81          | ~ (v1_funct_1 @ X0))),
% 5.59/5.81      inference('demod', [status(thm)], ['77', '78'])).
% 5.59/5.81  thf('80', plain,
% 5.59/5.81      ((~ (v1_funct_1 @ sk_D)
% 5.59/5.81        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.59/5.81            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['74', '79'])).
% 5.59/5.81  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('82', plain,
% 5.59/5.81      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.59/5.81         = (k6_partfun1 @ sk_A))),
% 5.59/5.81      inference('demod', [status(thm)], ['38', '41'])).
% 5.59/5.81  thf('83', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 5.59/5.81      inference('demod', [status(thm)], ['80', '81', '82'])).
% 5.59/5.81  thf(t45_relat_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( v1_relat_1 @ A ) =>
% 5.59/5.81       ( ![B:$i]:
% 5.59/5.81         ( ( v1_relat_1 @ B ) =>
% 5.59/5.81           ( r1_tarski @
% 5.59/5.81             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.59/5.81  thf('84', plain,
% 5.59/5.81      (![X29 : $i, X30 : $i]:
% 5.59/5.81         (~ (v1_relat_1 @ X29)
% 5.59/5.81          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X30 @ X29)) @ 
% 5.59/5.81             (k2_relat_1 @ X29))
% 5.59/5.81          | ~ (v1_relat_1 @ X30))),
% 5.59/5.81      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.59/5.81  thf('85', plain,
% 5.59/5.81      (![X7 : $i, X9 : $i]:
% 5.59/5.81         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 5.59/5.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.59/5.81  thf('86', plain,
% 5.59/5.81      (![X0 : $i, X1 : $i]:
% 5.59/5.81         (~ (v1_relat_1 @ X1)
% 5.59/5.81          | ~ (v1_relat_1 @ X0)
% 5.59/5.81          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.59/5.81               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.59/5.81          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.59/5.81      inference('sup-', [status(thm)], ['84', '85'])).
% 5.59/5.81  thf('87', plain,
% 5.59/5.81      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 5.59/5.81           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 5.59/5.81        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 5.59/5.81        | ~ (v1_relat_1 @ sk_D)
% 5.59/5.81        | ~ (v1_relat_1 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['83', '86'])).
% 5.59/5.81  thf('88', plain, (![X32 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X32)) = (X32))),
% 5.59/5.81      inference('demod', [status(thm)], ['2', '3'])).
% 5.59/5.81  thf('89', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(cc2_relset_1, axiom,
% 5.59/5.81    (![A:$i,B:$i,C:$i]:
% 5.59/5.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.59/5.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.59/5.81  thf('90', plain,
% 5.59/5.81      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.59/5.81         ((v5_relat_1 @ X35 @ X37)
% 5.59/5.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 5.59/5.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.59/5.81  thf('91', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 5.59/5.81      inference('sup-', [status(thm)], ['89', '90'])).
% 5.59/5.81  thf(d19_relat_1, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( v1_relat_1 @ B ) =>
% 5.59/5.81       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.59/5.81  thf('92', plain,
% 5.59/5.81      (![X24 : $i, X25 : $i]:
% 5.59/5.81         (~ (v5_relat_1 @ X24 @ X25)
% 5.59/5.81          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 5.59/5.81          | ~ (v1_relat_1 @ X24))),
% 5.59/5.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.59/5.81  thf('93', plain,
% 5.59/5.81      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 5.59/5.81      inference('sup-', [status(thm)], ['91', '92'])).
% 5.59/5.81  thf('94', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf(cc2_relat_1, axiom,
% 5.59/5.81    (![A:$i]:
% 5.59/5.81     ( ( v1_relat_1 @ A ) =>
% 5.59/5.81       ( ![B:$i]:
% 5.59/5.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.59/5.81  thf('95', plain,
% 5.59/5.81      (![X22 : $i, X23 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 5.59/5.81          | (v1_relat_1 @ X22)
% 5.59/5.81          | ~ (v1_relat_1 @ X23))),
% 5.59/5.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.59/5.81  thf('96', plain,
% 5.59/5.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.59/5.81      inference('sup-', [status(thm)], ['94', '95'])).
% 5.59/5.81  thf(fc6_relat_1, axiom,
% 5.59/5.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.59/5.81  thf('97', plain,
% 5.59/5.81      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.59/5.81  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 5.59/5.81      inference('demod', [status(thm)], ['96', '97'])).
% 5.59/5.81  thf('99', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 5.59/5.81      inference('demod', [status(thm)], ['93', '98'])).
% 5.59/5.81  thf('100', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 5.59/5.81      inference('demod', [status(thm)], ['80', '81', '82'])).
% 5.59/5.81  thf('101', plain,
% 5.59/5.81      (![X32 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X32)) = (X32))),
% 5.59/5.81      inference('demod', [status(thm)], ['2', '3'])).
% 5.59/5.81  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 5.59/5.81      inference('demod', [status(thm)], ['96', '97'])).
% 5.59/5.81  thf('103', plain,
% 5.59/5.81      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.59/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.59/5.81  thf('104', plain,
% 5.59/5.81      (![X22 : $i, X23 : $i]:
% 5.59/5.81         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 5.59/5.81          | (v1_relat_1 @ X22)
% 5.59/5.81          | ~ (v1_relat_1 @ X23))),
% 5.59/5.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.59/5.81  thf('105', plain,
% 5.59/5.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 5.59/5.81      inference('sup-', [status(thm)], ['103', '104'])).
% 5.59/5.81  thf('106', plain,
% 5.59/5.81      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 5.59/5.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.59/5.81  thf('107', plain, ((v1_relat_1 @ sk_C_1)),
% 5.59/5.81      inference('demod', [status(thm)], ['105', '106'])).
% 5.59/5.81  thf('108', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.59/5.81      inference('demod', [status(thm)],
% 5.59/5.81                ['87', '88', '99', '100', '101', '102', '107'])).
% 5.59/5.81  thf('109', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 5.59/5.81      inference('simplify', [status(thm)], ['63'])).
% 5.59/5.81  thf('110', plain,
% 5.59/5.81      (![X24 : $i, X25 : $i]:
% 5.59/5.81         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 5.59/5.81          | (v5_relat_1 @ X24 @ X25)
% 5.59/5.81          | ~ (v1_relat_1 @ X24))),
% 5.59/5.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.59/5.81  thf('111', plain,
% 5.59/5.81      (![X0 : $i]:
% 5.59/5.81         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 5.59/5.81      inference('sup-', [status(thm)], ['109', '110'])).
% 5.59/5.81  thf(d3_funct_2, axiom,
% 5.59/5.81    (![A:$i,B:$i]:
% 5.59/5.81     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.59/5.81       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.59/5.81  thf('112', plain,
% 5.59/5.81      (![X43 : $i, X44 : $i]:
% 5.59/5.81         (((k2_relat_1 @ X44) != (X43))
% 5.59/5.81          | (v2_funct_2 @ X44 @ X43)
% 5.59/5.81          | ~ (v5_relat_1 @ X44 @ X43)
% 5.59/5.81          | ~ (v1_relat_1 @ X44))),
% 5.59/5.81      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.59/5.81  thf('113', plain,
% 5.59/5.81      (![X44 : $i]:
% 5.59/5.81         (~ (v1_relat_1 @ X44)
% 5.59/5.81          | ~ (v5_relat_1 @ X44 @ (k2_relat_1 @ X44))
% 5.59/5.81          | (v2_funct_2 @ X44 @ (k2_relat_1 @ X44)))),
% 5.59/5.81      inference('simplify', [status(thm)], ['112'])).
% 5.59/5.81  thf('114', plain,
% 5.59/5.81      (![X0 : $i]:
% 5.59/5.81         (~ (v1_relat_1 @ X0)
% 5.59/5.81          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 5.59/5.81          | ~ (v1_relat_1 @ X0))),
% 5.59/5.81      inference('sup-', [status(thm)], ['111', '113'])).
% 5.59/5.81  thf('115', plain,
% 5.59/5.81      (![X0 : $i]:
% 5.59/5.81         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 5.59/5.81      inference('simplify', [status(thm)], ['114'])).
% 5.59/5.81  thf('116', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 5.59/5.81      inference('sup+', [status(thm)], ['108', '115'])).
% 5.59/5.81  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 5.59/5.81      inference('demod', [status(thm)], ['96', '97'])).
% 5.59/5.81  thf('118', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.59/5.81      inference('demod', [status(thm)], ['116', '117'])).
% 5.59/5.81  thf('119', plain, ($false), inference('demod', [status(thm)], ['73', '118'])).
% 5.59/5.81  
% 5.59/5.81  % SZS output end Refutation
% 5.59/5.81  
% 5.65/5.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
