%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oCUpBQf4L3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:41 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 207 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  733 (1778 expanded)
%              Number of equality atoms :   50 (  72 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i] :
      ( ( v1_xboole_0 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ X58 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X58 @ X59 ) @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X60: $i,X61: $i] :
      ( ( v1_xboole_0 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ X60 )
      | ( ( k6_domain_1 @ X60 @ X61 )
        = ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( v1_subset_1 @ X62 @ X63 )
      | ( v1_xboole_0 @ X62 )
      | ~ ( v1_zfmisc_1 @ X63 )
      | ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( r2_hidden @ X44 @ X53 )
      | ( X53
       != ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X44 @ ( k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 ) )
      | ( zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_zfmisc_1 @ X30 @ X31 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X30: $i] :
      ( ( k2_zfmisc_1 @ X30 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i] :
      ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','44'])).

thf('46',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('47',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X35 != X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X34: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['49','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oCUpBQf4L3
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.14/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.32  % Solved by: fo/fo7.sh
% 1.14/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.32  % done 1482 iterations in 0.870s
% 1.14/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.32  % SZS output start Refutation
% 1.14/1.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.14/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.32  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.14/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.14/1.32                                               $i > $i > $i > $o).
% 1.14/1.32  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.14/1.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.32  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.14/1.32  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.14/1.32  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.14/1.32  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.14/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.14/1.32  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.14/1.32                                           $i > $i).
% 1.14/1.32  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.14/1.32  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.14/1.32  thf(t6_tex_2, conjecture,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( m1_subset_1 @ B @ A ) =>
% 1.14/1.32           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.14/1.32                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.32    (~( ![A:$i]:
% 1.14/1.32        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.32          ( ![B:$i]:
% 1.14/1.32            ( ( m1_subset_1 @ B @ A ) =>
% 1.14/1.32              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.14/1.32                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 1.14/1.32    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 1.14/1.32  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(dt_k6_domain_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.14/1.32       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.14/1.32  thf('1', plain,
% 1.14/1.32      (![X58 : $i, X59 : $i]:
% 1.14/1.32         ((v1_xboole_0 @ X58)
% 1.14/1.32          | ~ (m1_subset_1 @ X59 @ X58)
% 1.14/1.32          | (m1_subset_1 @ (k6_domain_1 @ X58 @ X59) @ (k1_zfmisc_1 @ X58)))),
% 1.14/1.32      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.14/1.32  thf('2', plain,
% 1.14/1.32      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 1.14/1.32        | (v1_xboole_0 @ sk_A))),
% 1.14/1.32      inference('sup-', [status(thm)], ['0', '1'])).
% 1.14/1.32  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(redefinition_k6_domain_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.14/1.32       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.14/1.32  thf('4', plain,
% 1.14/1.32      (![X60 : $i, X61 : $i]:
% 1.14/1.32         ((v1_xboole_0 @ X60)
% 1.14/1.32          | ~ (m1_subset_1 @ X61 @ X60)
% 1.14/1.32          | ((k6_domain_1 @ X60 @ X61) = (k1_tarski @ X61)))),
% 1.14/1.32      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.14/1.32  thf('5', plain,
% 1.14/1.32      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 1.14/1.32        | (v1_xboole_0 @ sk_A))),
% 1.14/1.32      inference('sup-', [status(thm)], ['3', '4'])).
% 1.14/1.32  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 1.14/1.32      inference('clc', [status(thm)], ['5', '6'])).
% 1.14/1.32  thf('8', plain,
% 1.14/1.32      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 1.14/1.32        | (v1_xboole_0 @ sk_A))),
% 1.14/1.32      inference('demod', [status(thm)], ['2', '7'])).
% 1.14/1.32  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.14/1.32      inference('clc', [status(thm)], ['8', '9'])).
% 1.14/1.32  thf(cc2_tex_2, axiom,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.14/1.32           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 1.14/1.32  thf('11', plain,
% 1.14/1.32      (![X62 : $i, X63 : $i]:
% 1.14/1.32         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 1.14/1.32          | ~ (v1_subset_1 @ X62 @ X63)
% 1.14/1.32          | (v1_xboole_0 @ X62)
% 1.14/1.32          | ~ (v1_zfmisc_1 @ X63)
% 1.14/1.32          | (v1_xboole_0 @ X63))),
% 1.14/1.32      inference('cnf', [status(esa)], [cc2_tex_2])).
% 1.14/1.32  thf('12', plain,
% 1.14/1.32      (((v1_xboole_0 @ sk_A)
% 1.14/1.32        | ~ (v1_zfmisc_1 @ sk_A)
% 1.14/1.32        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 1.14/1.32        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 1.14/1.32      inference('sup-', [status(thm)], ['10', '11'])).
% 1.14/1.32  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 1.14/1.32      inference('clc', [status(thm)], ['5', '6'])).
% 1.14/1.32  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 1.14/1.32      inference('demod', [status(thm)], ['14', '15'])).
% 1.14/1.32  thf('17', plain,
% 1.14/1.32      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['12', '13', '16'])).
% 1.14/1.32  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 1.14/1.32      inference('clc', [status(thm)], ['17', '18'])).
% 1.14/1.32  thf(l13_xboole_0, axiom,
% 1.14/1.32    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.14/1.32  thf('20', plain,
% 1.14/1.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.14/1.32      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.14/1.32  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['19', '20'])).
% 1.14/1.32  thf(t69_enumset1, axiom,
% 1.14/1.32    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.14/1.32  thf('22', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 1.14/1.32      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.14/1.32  thf(t70_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.14/1.32  thf('23', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i]:
% 1.14/1.32         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.14/1.32      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.14/1.32  thf(t71_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.14/1.32  thf('24', plain,
% 1.14/1.32      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.14/1.32         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.14/1.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.14/1.32  thf(t72_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.32     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.14/1.32  thf('25', plain,
% 1.14/1.32      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.14/1.32         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 1.14/1.32           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 1.14/1.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.14/1.32  thf(t73_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.14/1.32     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.14/1.32       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.14/1.32  thf('26', plain,
% 1.14/1.32      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.14/1.32         ((k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15)
% 1.14/1.32           = (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 1.14/1.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.14/1.32  thf(t74_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.14/1.32     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.14/1.32       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.14/1.32  thf('27', plain,
% 1.14/1.32      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.14/1.32         ((k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 1.14/1.32           = (k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 1.14/1.32      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.14/1.32  thf(t75_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.14/1.32     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.14/1.32       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.14/1.32  thf('28', plain,
% 1.14/1.32      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.14/1.32         ((k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.14/1.32           = (k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 1.14/1.32      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.14/1.32  thf(d6_enumset1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.14/1.32     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.14/1.32       ( ![J:$i]:
% 1.14/1.32         ( ( r2_hidden @ J @ I ) <=>
% 1.14/1.32           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.14/1.32                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.14/1.32                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_1, type, zip_tseitin_0 :
% 1.14/1.32      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.14/1.32  thf(zf_stmt_2, axiom,
% 1.14/1.32    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.14/1.32     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.14/1.32       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.14/1.32         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.14/1.32         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_3, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.14/1.32     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.14/1.32       ( ![J:$i]:
% 1.14/1.32         ( ( r2_hidden @ J @ I ) <=>
% 1.14/1.32           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.14/1.32  thf('29', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 1.14/1.32         X51 : $i, X52 : $i, X53 : $i]:
% 1.14/1.32         ((zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 1.14/1.32          | (r2_hidden @ X44 @ X53)
% 1.14/1.32          | ((X53)
% 1.14/1.32              != (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.14/1.32  thf('30', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 1.14/1.32         X51 : $i, X52 : $i]:
% 1.14/1.32         ((r2_hidden @ X44 @ 
% 1.14/1.32           (k6_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45))
% 1.14/1.32          | (zip_tseitin_0 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ 
% 1.14/1.32             X52))),
% 1.14/1.32      inference('simplify', [status(thm)], ['29'])).
% 1.14/1.32  thf('31', plain,
% 1.14/1.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.14/1.32      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.14/1.32  thf(t113_zfmisc_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.14/1.32       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.14/1.32  thf('32', plain,
% 1.14/1.32      (![X30 : $i, X31 : $i]:
% 1.14/1.32         (((k2_zfmisc_1 @ X30 @ X31) = (k1_xboole_0))
% 1.14/1.32          | ((X31) != (k1_xboole_0)))),
% 1.14/1.32      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.14/1.32  thf('33', plain,
% 1.14/1.32      (![X30 : $i]: ((k2_zfmisc_1 @ X30 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.32      inference('simplify', [status(thm)], ['32'])).
% 1.14/1.32  thf(t152_zfmisc_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.14/1.32  thf('34', plain,
% 1.14/1.32      (![X32 : $i, X33 : $i]: ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X32 @ X33))),
% 1.14/1.32      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.14/1.32  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.32      inference('sup-', [status(thm)], ['33', '34'])).
% 1.14/1.32  thf('36', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['31', '35'])).
% 1.14/1.32  thf('37', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 1.14/1.32         X7 : $i, X8 : $i]:
% 1.14/1.32         ((zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 1.14/1.32          | ~ (v1_xboole_0 @ 
% 1.14/1.32               (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['30', '36'])).
% 1.14/1.32  thf('38', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.14/1.32      inference('sup-', [status(thm)], ['28', '37'])).
% 1.14/1.32  thf('39', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 1.14/1.32      inference('sup-', [status(thm)], ['27', '38'])).
% 1.14/1.32  thf('40', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 1.14/1.32      inference('sup-', [status(thm)], ['26', '39'])).
% 1.14/1.32  thf('41', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 1.14/1.32      inference('sup-', [status(thm)], ['25', '40'])).
% 1.14/1.32  thf('42', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 1.14/1.32      inference('sup-', [status(thm)], ['24', '41'])).
% 1.14/1.32  thf('43', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['23', '42'])).
% 1.14/1.32  thf('44', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 1.14/1.32          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['22', '43'])).
% 1.14/1.32  thf('45', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.14/1.32          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 1.14/1.32             sk_B @ sk_B))),
% 1.14/1.32      inference('sup-', [status(thm)], ['21', '44'])).
% 1.14/1.32  thf('46', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 1.14/1.32      inference('clc', [status(thm)], ['17', '18'])).
% 1.14/1.32  thf('47', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['19', '20'])).
% 1.14/1.32  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.14/1.32      inference('demod', [status(thm)], ['46', '47'])).
% 1.14/1.32  thf('49', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ 
% 1.14/1.32          sk_B @ sk_B)),
% 1.14/1.32      inference('demod', [status(thm)], ['45', '48'])).
% 1.14/1.32  thf('50', plain,
% 1.14/1.32      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 1.14/1.32         X41 : $i, X42 : $i]:
% 1.14/1.32         (((X35) != (X34))
% 1.14/1.32          | ~ (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ 
% 1.14/1.32               X34))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.14/1.32  thf('51', plain,
% 1.14/1.32      (![X34 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 1.14/1.32         X42 : $i]:
% 1.14/1.32         ~ (zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X34)),
% 1.14/1.32      inference('simplify', [status(thm)], ['50'])).
% 1.14/1.32  thf('52', plain, ($false), inference('sup-', [status(thm)], ['49', '51'])).
% 1.14/1.32  
% 1.14/1.32  % SZS output end Refutation
% 1.14/1.32  
% 1.14/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
