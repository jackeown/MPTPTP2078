%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kdVK8Aun3g

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 124 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  471 ( 742 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','40'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('42',plain,(
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

thf('43',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X23: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['41','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kdVK8Aun3g
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 71 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.50  thf(t6_tex_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.50           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.50                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.50              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.50                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.50  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X27)
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ X27)
% 0.21/0.50          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.50        | (v1_xboole_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X24)
% 0.21/0.51          | ~ (m1_subset_1 @ X25 @ X24)
% 0.21/0.51          | (m1_subset_1 @ (k6_domain_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(t1_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.51           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X33 : $i, X34 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X33)
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X33)
% 0.21/0.51          | ((X34) = (X33))
% 0.21/0.51          | ~ (r1_tarski @ X34 @ X33)
% 0.21/0.51          | (v1_xboole_0 @ X34))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.51        | ((k1_tarski @ sk_B) = (sk_A))
% 0.21/0.51        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.51        | ((k1_tarski @ sk_B) = (sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('24', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X13 : $i, X15 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(t5_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X19 @ X20)
% 0.21/0.51          | ~ (v1_xboole_0 @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.51  thf(t4_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (sk_A)) | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '35'])).
% 0.21/0.51  thf(t1_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('37', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.51  thf(t49_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.51  thf('39', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['36', '39'])).
% 0.21/0.51  thf('41', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '40'])).
% 0.21/0.51  thf(dt_l1_orders_2, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_orders_2 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.51  thf(t1_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.51       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf(fc12_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X23 : $i]:
% 0.21/0.51         (~ (v1_subset_1 @ (k2_struct_0 @ X23) @ (u1_struct_0 @ X23))
% 0.21/0.51          | ~ (l1_struct_0 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_orders_2 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.21/0.51          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.51  thf(dt_k2_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.51       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.51  thf('51', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('52', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '53'])).
% 0.21/0.51  thf('55', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('56', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, ($false), inference('sup-', [status(thm)], ['41', '56'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
