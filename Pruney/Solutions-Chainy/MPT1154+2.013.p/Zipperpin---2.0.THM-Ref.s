%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Wg3x5a626

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:49 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 195 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          : 1346 (2503 expanded)
%              Number of equality atoms :   62 (  78 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(zf_stmt_0,axiom,(
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

thf('0',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      | ( X32 = X33 )
      | ( X32 = X34 )
      | ( X32 = X35 )
      | ( X32 = X36 )
      | ( X32 = X37 )
      | ( X32 = X38 )
      | ( X32 = X39 )
      | ( X32 = X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X51 @ X50 )
      | ~ ( zip_tseitin_0 @ X51 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      | ( X50
       != ( k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      | ~ ( r2_hidden @ X51 @ ( k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

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

thf(zf_stmt_3,negated_conjecture,(
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

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X61: $i,X62: $i] :
      ( ( v1_xboole_0 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ X61 )
      | ( ( k6_domain_1 @ X61 @ X62 )
        = ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('26',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_B_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X64 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X64 ) @ X63 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( l1_orders_2 @ X64 )
      | ~ ( v3_orders_2 @ X64 )
      | ( v2_struct_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

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

thf('36',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( u1_struct_0 @ X66 ) )
      | ~ ( r2_hidden @ X65 @ ( k1_orders_2 @ X66 @ X67 ) )
      | ~ ( r2_hidden @ X65 @ X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ~ ( l1_orders_2 @ X66 )
      | ~ ( v5_orders_2 @ X66 )
      | ~ ( v4_orders_2 @ X66 )
      | ~ ( v3_orders_2 @ X66 )
      | ( v2_struct_0 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','47'])).

thf('49',plain,(
    r2_hidden @ sk_B_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(dt_k1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( l1_orders_2 @ X59 )
      | ~ ( v5_orders_2 @ X59 )
      | ~ ( v4_orders_2 @ X59 )
      | ~ ( v3_orders_2 @ X59 )
      | ( v2_struct_0 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( m1_subset_1 @ ( k1_orders_2 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_orders_2])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('60',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('73',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('74',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      | ( r2_hidden @ X41 @ X50 )
      | ( X50
       != ( k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ X41 @ ( k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 ) )
      | ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','84'])).

thf('86',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X32 != X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X31: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X31 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference('sup-',[status(thm)],['85','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Wg3x5a626
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 209 iterations in 0.132s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.59  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.39/0.59                                           $i > $i).
% 0.39/0.59  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.59  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.39/0.59  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.39/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.39/0.59                                               $i > $i > $i > $o).
% 0.39/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.59  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(d6_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.39/0.59     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.39/0.59       ( ![J:$i]:
% 0.39/0.59         ( ( r2_hidden @ J @ I ) <=>
% 0.39/0.59           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.39/0.59                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.39/0.59                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, axiom,
% 0.39/0.59    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.39/0.59       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.39/0.59         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.39/0.59         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.39/0.59         X39 : $i, X40 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.39/0.59          | ((X32) = (X33))
% 0.39/0.59          | ((X32) = (X34))
% 0.39/0.59          | ((X32) = (X35))
% 0.39/0.59          | ((X32) = (X36))
% 0.39/0.59          | ((X32) = (X37))
% 0.39/0.59          | ((X32) = (X38))
% 0.39/0.59          | ((X32) = (X39))
% 0.39/0.59          | ((X32) = (X40)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d1_xboole_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf(t69_enumset1, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.59  thf('2', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf(t70_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X4 : $i, X5 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf(t71_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf(t72_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.39/0.59           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.39/0.59  thf(t73_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.39/0.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.39/0.59           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.39/0.59  thf(t74_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.59     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.39/0.59       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.59         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.39/0.59           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.39/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.39/0.59  thf(t75_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.59     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.39/0.59       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.59         ((k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.39/0.59           = (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.39/0.59      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.39/0.59  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.39/0.59      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.39/0.59     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.39/0.59       ( ![J:$i]:
% 0.39/0.59         ( ( r2_hidden @ J @ I ) <=>
% 0.39/0.59           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.39/0.59         X49 : $i, X50 : $i, X51 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X51 @ X50)
% 0.39/0.59          | ~ (zip_tseitin_0 @ X51 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ 
% 0.39/0.59               X49)
% 0.39/0.59          | ((X50)
% 0.39/0.59              != (k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.39/0.59         X49 : $i, X51 : $i]:
% 0.39/0.59         (~ (zip_tseitin_0 @ X51 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ 
% 0.39/0.59             X49)
% 0.39/0.59          | ~ (r2_hidden @ X51 @ 
% 0.39/0.59               (k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '15'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '16'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0 @ X0 @ 
% 0.39/0.59               X0 @ X0 @ X0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.39/0.59          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.39/0.59          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.39/0.59          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.39/0.59          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.59  thf(t48_orders_2, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59           ( ~( r2_hidden @
% 0.39/0.59                B @ 
% 0.39/0.59                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_3, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59              ( ~( r2_hidden @
% 0.39/0.59                   B @ 
% 0.39/0.59                   ( k1_orders_2 @
% 0.39/0.59                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.39/0.59  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X61 : $i, X62 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ X61)
% 0.39/0.59          | ~ (m1_subset_1 @ X62 @ X61)
% 0.39/0.59          | ((k6_domain_1 @ X61 @ X62) = (k1_tarski @ X62)))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.39/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((r2_hidden @ sk_B_1 @ 
% 0.39/0.59        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf(t35_orders_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.39/0.59             ( m1_subset_1 @
% 0.39/0.59               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.59               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X63 : $i, X64 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X64))
% 0.39/0.59          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X64) @ X63) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 0.39/0.59          | ~ (l1_orders_2 @ X64)
% 0.39/0.59          | ~ (v3_orders_2 @ X64)
% 0.39/0.59          | (v2_struct_0 @ X64))),
% 0.39/0.59      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.59        | ~ (l1_orders_2 @ sk_A)
% 0.39/0.59        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.59  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.39/0.59  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf(t47_orders_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59               ( ~( ( r2_hidden @ B @ C ) & 
% 0.39/0.59                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X65 @ (u1_struct_0 @ X66))
% 0.39/0.59          | ~ (r2_hidden @ X65 @ (k1_orders_2 @ X66 @ X67))
% 0.39/0.59          | ~ (r2_hidden @ X65 @ X67)
% 0.39/0.59          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 0.39/0.59          | ~ (l1_orders_2 @ X66)
% 0.39/0.59          | ~ (v5_orders_2 @ X66)
% 0.39/0.59          | ~ (v4_orders_2 @ X66)
% 0.39/0.59          | ~ (v3_orders_2 @ X66)
% 0.39/0.59          | (v2_struct_0 @ X66))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v3_orders_2 @ sk_A)
% 0.39/0.59          | ~ (v4_orders_2 @ sk_A)
% 0.39/0.59          | ~ (v5_orders_2 @ sk_A)
% 0.39/0.59          | ~ (l1_orders_2 @ sk_A)
% 0.39/0.59          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.39/0.59          | ~ (r2_hidden @ X0 @ 
% 0.39/0.59               (k1_orders_2 @ sk_A @ 
% 0.39/0.59                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('39', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.39/0.59          | ~ (r2_hidden @ X0 @ 
% 0.39/0.59               (k1_orders_2 @ sk_A @ 
% 0.39/0.59                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['27', '42'])).
% 0.39/0.59  thf('44', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      ((~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.39/0.59      inference('clc', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      ((~ (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1))
% 0.39/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      ((r2_hidden @ sk_B_1 @ 
% 0.39/0.59        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf(dt_k1_orders_2, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.39/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.59       ( m1_subset_1 @
% 0.39/0.59         ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X59 : $i, X60 : $i]:
% 0.39/0.59         (~ (l1_orders_2 @ X59)
% 0.39/0.59          | ~ (v5_orders_2 @ X59)
% 0.39/0.59          | ~ (v4_orders_2 @ X59)
% 0.39/0.59          | ~ (v3_orders_2 @ X59)
% 0.39/0.59          | (v2_struct_0 @ X59)
% 0.39/0.59          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 0.39/0.59          | (m1_subset_1 @ (k1_orders_2 @ X59 @ X60) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X59))))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k1_orders_2])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (((m1_subset_1 @ 
% 0.39/0.59         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59        | (v2_struct_0 @ sk_A)
% 0.39/0.59        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v4_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v5_orders_2 @ sk_A)
% 0.39/0.59        | ~ (l1_orders_2 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.59  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (((m1_subset_1 @ 
% 0.39/0.59         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.39/0.59  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      ((m1_subset_1 @ 
% 0.39/0.59        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['57', '58'])).
% 0.39/0.59  thf(l3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X53 @ X54)
% 0.39/0.59          | (r2_hidden @ X53 @ X55)
% 0.39/0.59          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.59          | ~ (r2_hidden @ X0 @ 
% 0.39/0.59               (k1_orders_2 @ sk_A @ 
% 0.39/0.59                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.59  thf('62', plain, ((r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['49', '61'])).
% 0.39/0.59  thf('63', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('64', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.59  thf('65', plain, (~ (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1))),
% 0.39/0.59      inference('clc', [status(thm)], ['48', '64'])).
% 0.39/0.59  thf('66', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '65'])).
% 0.39/0.59  thf('67', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      (![X4 : $i, X5 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.39/0.59           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.39/0.59           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.59         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.41/0.59           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.59         ((k6_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.41/0.59           = (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.41/0.59      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.41/0.59         X48 : $i, X49 : $i, X50 : $i]:
% 0.41/0.59         ((zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.41/0.59          | (r2_hidden @ X41 @ X50)
% 0.41/0.59          | ((X50)
% 0.41/0.59              != (k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.41/0.59         X48 : $i, X49 : $i]:
% 0.41/0.59         ((r2_hidden @ X41 @ 
% 0.41/0.59           (k6_enumset1 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42))
% 0.41/0.59          | (zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ 
% 0.41/0.59             X49))),
% 0.41/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.41/0.59  thf('76', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.41/0.59         X7 : $i, X8 : $i]:
% 0.41/0.59         ((zip_tseitin_0 @ X8 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.41/0.59          | ~ (v1_xboole_0 @ 
% 0.41/0.59               (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.59  thf('78', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.41/0.59      inference('sup-', [status(thm)], ['73', '77'])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 @ X5))),
% 0.41/0.59      inference('sup-', [status(thm)], ['72', '78'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 @ X4))),
% 0.41/0.59      inference('sup-', [status(thm)], ['71', '79'])).
% 0.41/0.59  thf('81', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 @ X3))),
% 0.41/0.59      inference('sup-', [status(thm)], ['70', '80'])).
% 0.41/0.59  thf('82', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['69', '81'])).
% 0.41/0.59  thf('83', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['68', '82'])).
% 0.41/0.59  thf('84', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.41/0.59          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['67', '83'])).
% 0.41/0.59  thf('85', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.59          sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.41/0.59      inference('sup-', [status(thm)], ['66', '84'])).
% 0.41/0.59  thf('86', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.41/0.59         X38 : $i, X39 : $i]:
% 0.41/0.59         (((X32) != (X31))
% 0.41/0.59          | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ 
% 0.41/0.59               X31))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('87', plain,
% 0.41/0.59      (![X31 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.41/0.59         X39 : $i]:
% 0.41/0.59         ~ (zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X31)),
% 0.41/0.59      inference('simplify', [status(thm)], ['86'])).
% 0.41/0.59  thf('88', plain, ($false), inference('sup-', [status(thm)], ['85', '87'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
