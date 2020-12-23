%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EISNlTmfUT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  534 (1106 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X29 @ ( k1_orders_2 @ X30 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v5_orders_2 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X12 @ X17 )
      | ( X17
       != ( k2_enumset1 @ X16 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X12 @ ( k2_enumset1 @ X16 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X10 @ X6 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','36'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EISNlTmfUT
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:00:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 61 iterations in 0.031s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.19/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.48  thf(t48_orders_2, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ~( r2_hidden @
% 0.19/0.48                B @ 
% 0.19/0.48                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48              ( ~( r2_hidden @
% 0.19/0.48                   B @ 
% 0.19/0.48                   ( k1_orders_2 @
% 0.19/0.48                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.19/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X25)
% 0.19/0.48          | ~ (m1_subset_1 @ X26 @ X25)
% 0.19/0.48          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((r2_hidden @ sk_B @ 
% 0.19/0.48        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t35_orders_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.19/0.48             ( m1_subset_1 @
% 0.19/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.19/0.48               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X27 : $i, X28 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.19/0.48          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.48          | ~ (l1_orders_2 @ X28)
% 0.19/0.48          | ~ (v3_orders_2 @ X28)
% 0.19/0.48          | (v2_struct_0 @ X28))),
% 0.19/0.48      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.19/0.48        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.48  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf(t47_orders_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48               ( ~( ( r2_hidden @ B @ C ) & 
% 0.19/0.48                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.19/0.48          | ~ (r2_hidden @ X29 @ (k1_orders_2 @ X30 @ X31))
% 0.19/0.48          | ~ (r2_hidden @ X29 @ X31)
% 0.19/0.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.19/0.48          | ~ (l1_orders_2 @ X30)
% 0.19/0.48          | ~ (v5_orders_2 @ X30)
% 0.19/0.48          | ~ (v4_orders_2 @ X30)
% 0.19/0.48          | ~ (v3_orders_2 @ X30)
% 0.19/0.48          | (v2_struct_0 @ X30))),
% 0.19/0.48      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ 
% 0.19/0.48               (k1_orders_2 @ sk_A @ 
% 0.19/0.48                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ 
% 0.19/0.48               (k1_orders_2 @ sk_A @ 
% 0.19/0.48                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.48        | ~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '19'])).
% 0.19/0.48  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '24'])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('26', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf(t70_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.48  thf(t71_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.48  thf(d2_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=>
% 0.19/0.48           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.19/0.48                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_2, axiom,
% 0.19/0.48    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.19/0.48       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.19/0.48         ( ( F ) != ( D ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_3, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.19/0.48       ( ![F:$i]:
% 0.19/0.48         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.19/0.48          | (r2_hidden @ X12 @ X17)
% 0.19/0.48          | ((X17) != (k2_enumset1 @ X16 @ X15 @ X14 @ X13)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         ((r2_hidden @ X12 @ (k2_enumset1 @ X16 @ X15 @ X14 @ X13))
% 0.19/0.48          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.19/0.48      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.19/0.48          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.19/0.48      inference('sup+', [status(thm)], ['28', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X10 @ X6)),
% 0.19/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['27', '34'])).
% 0.19/0.48  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['26', '35'])).
% 0.19/0.48  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '36'])).
% 0.19/0.48  thf(fc2_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X23 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.19/0.48          | ~ (l1_struct_0 @ X23)
% 0.19/0.48          | (v2_struct_0 @ X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.48  thf('39', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.48  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_l1_orders_2, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_orders_2 @ X24))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.48  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['39', '42'])).
% 0.19/0.48  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.33/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
