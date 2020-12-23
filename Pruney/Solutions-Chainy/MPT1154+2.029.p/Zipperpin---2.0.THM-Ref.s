%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIQYBKUsrH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 119 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  762 (1272 expanded)
%              Number of equality atoms :   38 (  40 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t48_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X57: $i,X58: $i] :
      ( ( v1_xboole_0 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ X57 )
      | ( ( k6_domain_1 @ X57 @ X58 )
        = ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X54: $i,X55: $i] :
      ( ( v1_xboole_0 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ X54 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X54 @ X55 ) @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t47_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( u1_struct_0 @ X60 ) )
      | ~ ( r2_hidden @ X59 @ ( k1_orders_2 @ X60 @ X61 ) )
      | ~ ( r2_hidden @ X59 @ X61 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( l1_orders_2 @ X60 )
      | ~ ( v5_orders_2 @ X60 )
      | ~ ( v4_orders_2 @ X60 )
      | ~ ( v3_orders_2 @ X60 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
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

thf('32',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X38 @ X47 )
      | ( X47
       != ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X38 @ ( k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','42'])).

thf('44',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X53: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X53 ) )
      | ~ ( l1_struct_0 @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X56: $i] :
      ( ( l1_struct_0 @ X56 )
      | ~ ( l1_orders_2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIQYBKUsrH
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:23:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 86 iterations in 0.053s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.23/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.23/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.23/0.53                                           $i > $i).
% 0.23/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.23/0.53                                               $i > $i > $i > $o).
% 0.23/0.53  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.23/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.23/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.23/0.53  thf(t48_orders_2, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.53           ( ~( r2_hidden @
% 0.23/0.53                B @ 
% 0.23/0.53                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.53              ( ~( r2_hidden @
% 0.23/0.53                   B @ 
% 0.23/0.53                   ( k1_orders_2 @
% 0.23/0.53                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.23/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X57 : $i, X58 : $i]:
% 0.23/0.53         ((v1_xboole_0 @ X57)
% 0.23/0.53          | ~ (m1_subset_1 @ X58 @ X57)
% 0.23/0.53          | ((k6_domain_1 @ X57 @ X58) = (k1_tarski @ X58)))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      ((r2_hidden @ sk_B @ 
% 0.23/0.53        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_k6_domain_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X54 : $i, X55 : $i]:
% 0.23/0.53         ((v1_xboole_0 @ X54)
% 0.23/0.53          | ~ (m1_subset_1 @ X55 @ X54)
% 0.23/0.53          | (m1_subset_1 @ (k6_domain_1 @ X54 @ X55) @ (k1_zfmisc_1 @ X54)))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.23/0.53  thf('9', plain,
% 0.23/0.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.23/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.23/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.53  thf(t47_orders_2, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.53               ( ~( ( r2_hidden @ B @ C ) & 
% 0.23/0.53                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf('12', plain,
% 0.23/0.53      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X59 @ (u1_struct_0 @ X60))
% 0.23/0.53          | ~ (r2_hidden @ X59 @ (k1_orders_2 @ X60 @ X61))
% 0.23/0.53          | ~ (r2_hidden @ X59 @ X61)
% 0.23/0.53          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.23/0.53          | ~ (l1_orders_2 @ X60)
% 0.23/0.53          | ~ (v5_orders_2 @ X60)
% 0.23/0.53          | ~ (v4_orders_2 @ X60)
% 0.23/0.53          | ~ (v3_orders_2 @ X60)
% 0.23/0.53          | (v2_struct_0 @ X60))),
% 0.23/0.53      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.23/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.53  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.23/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.23/0.53        | (v2_struct_0 @ sk_A)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['5', '18'])).
% 0.23/0.53  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.23/0.53        | (v2_struct_0 @ sk_A)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_A)
% 0.23/0.53        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.53  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 0.23/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf(t69_enumset1, axiom,
% 0.23/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.53  thf('25', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.53  thf(t70_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      (![X1 : $i, X2 : $i]:
% 0.23/0.53         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.23/0.53  thf(t71_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.23/0.53  thf(t72_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.53         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.23/0.53           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.23/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.23/0.53  thf(t73_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.23/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.53         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.23/0.53           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.23/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.23/0.53  thf(t74_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.23/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.53         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.23/0.53           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.23/0.53  thf(t75_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.23/0.53     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.23/0.53       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.23/0.53  thf('31', plain,
% 0.23/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.23/0.53         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.23/0.53           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.23/0.53      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.23/0.53  thf(d6_enumset1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.53     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.23/0.53       ( ![J:$i]:
% 0.23/0.53         ( ( r2_hidden @ J @ I ) <=>
% 0.23/0.53           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.23/0.53                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.23/0.53                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.23/0.53      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.23/0.53  thf(zf_stmt_2, axiom,
% 0.23/0.53    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.23/0.53     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.23/0.53       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.23/0.53         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.23/0.53         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_3, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.23/0.53     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.23/0.53       ( ![J:$i]:
% 0.23/0.53         ( ( r2_hidden @ J @ I ) <=>
% 0.23/0.53           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.23/0.53         X45 : $i, X46 : $i, X47 : $i]:
% 0.23/0.53         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.23/0.53          | (r2_hidden @ X38 @ X47)
% 0.23/0.53          | ((X47)
% 0.23/0.53              != (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.53  thf('33', plain,
% 0.23/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.23/0.53         X45 : $i, X46 : $i]:
% 0.23/0.53         ((r2_hidden @ X38 @ 
% 0.23/0.53           (k6_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39))
% 0.23/0.53          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ 
% 0.23/0.53             X46))),
% 0.23/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.53  thf('34', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.53         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.53          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.23/0.53      inference('sup+', [status(thm)], ['31', '33'])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.23/0.53         X35 : $i, X36 : $i]:
% 0.23/0.53         (((X29) != (X28))
% 0.23/0.53          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ 
% 0.23/0.53               X28))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.23/0.53         X36 : $i]:
% 0.23/0.53         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X28)),
% 0.23/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.53         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.23/0.53      inference('sup-', [status(thm)], ['34', '36'])).
% 0.23/0.53  thf('38', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['30', '37'])).
% 0.23/0.53  thf('39', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['29', '38'])).
% 0.23/0.53  thf('40', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.53         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['28', '39'])).
% 0.23/0.53  thf('41', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['27', '40'])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['26', '41'])).
% 0.23/0.53  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['25', '42'])).
% 0.23/0.53  thf('44', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['24', '43'])).
% 0.23/0.53  thf(fc2_struct_0, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (![X53 : $i]:
% 0.23/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X53))
% 0.23/0.53          | ~ (l1_struct_0 @ X53)
% 0.23/0.53          | (v2_struct_0 @ X53))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.53  thf('46', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.53  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_l1_orders_2, axiom,
% 0.23/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      (![X56 : $i]: ((l1_struct_0 @ X56) | ~ (l1_orders_2 @ X56))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.23/0.53  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.23/0.53  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('demod', [status(thm)], ['46', '49'])).
% 0.23/0.53  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
