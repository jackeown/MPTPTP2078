%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XqNZp7PRVw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 125 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  484 ( 740 expanded)
%              Number of equality atoms :   40 (  46 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('25',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_subset_1 @ sk_A @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['26','41'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['47','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XqNZp7PRVw
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 145 iterations in 0.088s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.55  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.55  thf(t6_tex_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.55           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.55                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.55              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.55                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.20/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k6_domain_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X25 @ X24)
% 0.20/0.55          | (m1_subset_1 @ (k6_domain_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X27)
% 0.20/0.55          | ~ (m1_subset_1 @ X28 @ X27)
% 0.20/0.55          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '7'])).
% 0.20/0.55  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(t1_tex_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X33)
% 0.20/0.55          | ~ (v1_zfmisc_1 @ X33)
% 0.20/0.55          | ((X34) = (X33))
% 0.20/0.55          | ~ (r1_tarski @ X34 @ X33)
% 0.20/0.55          | (v1_xboole_0 @ X34))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.20/0.55        | ((k1_tarski @ sk_B) = (sk_A))
% 0.20/0.55        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.20/0.55        | ((k1_tarski @ sk_B) = (sk_A))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((((k1_tarski @ sk_B) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.20/0.55      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.55  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf(t8_boole, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((((k1_tarski @ sk_B) = (sk_A)) | ((k1_xboole_0) = (k1_tarski @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.55  thf('23', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('25', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((v1_subset_1 @ sk_A @ sk_A) | ((k1_xboole_0) = (k1_tarski @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf(dt_l1_orders_2, axiom,
% 0.20/0.55    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_orders_2 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.55  thf(t1_yellow_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.55       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.55  thf(fc12_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) =>
% 0.20/0.55       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X23 : $i]:
% 0.20/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ X23) @ (u1_struct_0 @ X23))
% 0.20/0.55          | ~ (l1_struct_0 @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_orders_2 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.55  thf(d3_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.20/0.55          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.55          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.55  thf(dt_k2_yellow_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.55       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.55  thf('36', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.55  thf('37', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['30', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '38'])).
% 0.20/0.55  thf('40', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.55  thf('41', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, (((k1_xboole_0) = (k1_tarski @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['26', '41'])).
% 0.20/0.55  thf(d1_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('44', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.20/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.55  thf(t7_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.55  thf('46', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_B)),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '46'])).
% 0.20/0.55  thf(commutativity_k2_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.55  thf(l51_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf(t1_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.55  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf(t7_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.55  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain, ($false), inference('demod', [status(thm)], ['47', '56'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
