%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uuM2rTnooX

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:29 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 159 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  510 (1091 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
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
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_zfmisc_1 @ X32 )
      | ( X33 = X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','26'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ~ ( v1_pre_topc @ X18 )
      | ( X18
        = ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( g1_pre_topc @ X26 @ X27 )
       != ( g1_pre_topc @ X24 @ X25 ) )
      | ( X26 = X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ X0 @ k1_xboole_0 )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ X1 @ k1_xboole_0 )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( g1_pre_topc @ X1 @ k1_xboole_0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X1 @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( l1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( v1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( g1_pre_topc @ X1 @ k1_xboole_0 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['36','39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_struct_0 @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( l1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_struct_0 @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X23: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_struct_0 @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('54',plain,(
    ! [X0: $i] :
      ( l1_pre_topc @ ( g1_pre_topc @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uuM2rTnooX
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:04:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.53  % Solved by: fo/fo7.sh
% 0.38/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.53  % done 93 iterations in 0.054s
% 0.38/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.53  % SZS output start Refutation
% 0.38/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.38/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.38/0.53  thf(t6_tex_2, conjecture,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.53       ( ![B:$i]:
% 0.38/0.53         ( ( m1_subset_1 @ B @ A ) =>
% 0.38/0.53           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.38/0.53                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.38/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.53    (~( ![A:$i]:
% 0.38/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.53          ( ![B:$i]:
% 0.38/0.53            ( ( m1_subset_1 @ B @ A ) =>
% 0.38/0.53              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.38/0.53                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.38/0.53    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.38/0.53  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.53  thf('2', plain,
% 0.38/0.53      (![X30 : $i, X31 : $i]:
% 0.38/0.53         ((v1_xboole_0 @ X30)
% 0.38/0.53          | ~ (m1_subset_1 @ X31 @ X30)
% 0.38/0.53          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 0.38/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.53  thf('3', plain,
% 0.38/0.53      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.38/0.53        | (v1_xboole_0 @ sk_A))),
% 0.38/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.53  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.38/0.53      inference('clc', [status(thm)], ['3', '4'])).
% 0.38/0.53  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.38/0.53      inference('demod', [status(thm)], ['0', '5'])).
% 0.38/0.53  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf(dt_k6_domain_1, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.53  thf('8', plain,
% 0.38/0.53      (![X28 : $i, X29 : $i]:
% 0.38/0.53         ((v1_xboole_0 @ X28)
% 0.38/0.53          | ~ (m1_subset_1 @ X29 @ X28)
% 0.38/0.53          | (m1_subset_1 @ (k6_domain_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28)))),
% 0.38/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.53  thf('9', plain,
% 0.38/0.53      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.53        | (v1_xboole_0 @ sk_A))),
% 0.38/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.53  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.38/0.53      inference('clc', [status(thm)], ['3', '4'])).
% 0.38/0.53  thf('11', plain,
% 0.38/0.53      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.53        | (v1_xboole_0 @ sk_A))),
% 0.38/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.53  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf('13', plain,
% 0.38/0.53      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.53  thf(t3_subset, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.53  thf('14', plain,
% 0.38/0.53      (![X12 : $i, X13 : $i]:
% 0.38/0.53         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.53  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.38/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.53  thf(t1_tex_2, axiom,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.53       ( ![B:$i]:
% 0.38/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.38/0.53           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.38/0.53  thf('16', plain,
% 0.38/0.53      (![X32 : $i, X33 : $i]:
% 0.38/0.53         ((v1_xboole_0 @ X32)
% 0.38/0.53          | ~ (v1_zfmisc_1 @ X32)
% 0.38/0.53          | ((X33) = (X32))
% 0.38/0.53          | ~ (r1_tarski @ X33 @ X32)
% 0.38/0.53          | (v1_xboole_0 @ X33))),
% 0.38/0.53      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.38/0.53  thf('17', plain,
% 0.38/0.53      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.38/0.53        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.38/0.53        | ~ (v1_zfmisc_1 @ sk_A)
% 0.38/0.53        | (v1_xboole_0 @ sk_A))),
% 0.38/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.53  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf('19', plain,
% 0.38/0.53      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.38/0.53        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.38/0.53        | (v1_xboole_0 @ sk_A))),
% 0.38/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.53  thf(d1_tarski, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.53  thf('20', plain,
% 0.38/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.53         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.38/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.53  thf('21', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.38/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.53  thf(d1_xboole_0, axiom,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.53  thf('22', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.53  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.53  thf('24', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.38/0.53      inference('clc', [status(thm)], ['19', '23'])).
% 0.38/0.53  thf('25', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.53  thf('26', plain, (((k1_tarski @ sk_B_1) = (sk_A))),
% 0.38/0.53      inference('clc', [status(thm)], ['24', '25'])).
% 0.38/0.53  thf('27', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.38/0.53      inference('demod', [status(thm)], ['6', '26'])).
% 0.38/0.53  thf(dt_l1_pre_topc, axiom,
% 0.38/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.53  thf('28', plain,
% 0.38/0.53      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.53  thf(d3_struct_0, axiom,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.53  thf('29', plain,
% 0.38/0.53      (![X19 : $i]:
% 0.38/0.53         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.38/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.53  thf('30', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.53  thf(abstractness_v1_pre_topc, axiom,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( l1_pre_topc @ A ) =>
% 0.38/0.53       ( ( v1_pre_topc @ A ) =>
% 0.38/0.53         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.38/0.53  thf('31', plain,
% 0.38/0.53      (![X18 : $i]:
% 0.38/0.53         (~ (v1_pre_topc @ X18)
% 0.38/0.53          | ((X18) = (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.38/0.53          | ~ (l1_pre_topc @ X18))),
% 0.38/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.38/0.53  thf(t4_subset_1, axiom,
% 0.38/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.53  thf('32', plain,
% 0.38/0.53      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.53  thf(free_g1_pre_topc, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.53       ( ![C:$i,D:$i]:
% 0.38/0.53         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.38/0.53           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.38/0.53  thf('33', plain,
% 0.38/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.53         (((g1_pre_topc @ X26 @ X27) != (g1_pre_topc @ X24 @ X25))
% 0.38/0.53          | ((X26) = (X24))
% 0.38/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26))))),
% 0.38/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.38/0.53  thf('34', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.53         (((X0) = (X1))
% 0.38/0.53          | ((g1_pre_topc @ X0 @ k1_xboole_0) != (g1_pre_topc @ X1 @ X2)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.53  thf('35', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]:
% 0.38/0.53         (((g1_pre_topc @ X1 @ k1_xboole_0) != (X0))
% 0.38/0.53          | ~ (l1_pre_topc @ X0)
% 0.38/0.53          | ~ (v1_pre_topc @ X0)
% 0.38/0.53          | ((X1) = (u1_struct_0 @ X0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.38/0.53  thf('36', plain,
% 0.38/0.53      (![X1 : $i]:
% 0.38/0.53         (((X1) = (u1_struct_0 @ (g1_pre_topc @ X1 @ k1_xboole_0)))
% 0.38/0.53          | ~ (v1_pre_topc @ (g1_pre_topc @ X1 @ k1_xboole_0))
% 0.38/0.53          | ~ (l1_pre_topc @ (g1_pre_topc @ X1 @ k1_xboole_0)))),
% 0.38/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.53  thf('37', plain,
% 0.38/0.53      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.53  thf(dt_g1_pre_topc, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.53       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.38/0.53         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.38/0.53  thf('38', plain,
% 0.38/0.53      (![X20 : $i, X21 : $i]:
% 0.38/0.53         ((l1_pre_topc @ (g1_pre_topc @ X20 @ X21))
% 0.38/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.53      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.38/0.53  thf('39', plain,
% 0.38/0.53      (![X0 : $i]: (l1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.53  thf('40', plain,
% 0.38/0.53      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.53  thf('41', plain,
% 0.38/0.53      (![X20 : $i, X21 : $i]:
% 0.38/0.53         ((v1_pre_topc @ (g1_pre_topc @ X20 @ X21))
% 0.38/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.53      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.38/0.53  thf('42', plain,
% 0.38/0.53      (![X0 : $i]: (v1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.53  thf('43', plain,
% 0.38/0.53      (![X1 : $i]: ((X1) = (u1_struct_0 @ (g1_pre_topc @ X1 @ k1_xboole_0)))),
% 0.38/0.53      inference('simplify_reflect+', [status(thm)], ['36', '39', '42'])).
% 0.38/0.53  thf('44', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (((X0) = (k2_struct_0 @ (g1_pre_topc @ X0 @ k1_xboole_0)))
% 0.38/0.53          | ~ (l1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0)))),
% 0.38/0.53      inference('sup+', [status(thm)], ['30', '43'])).
% 0.38/0.53  thf('45', plain,
% 0.38/0.53      (![X0 : $i]: (l1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.53  thf('46', plain,
% 0.38/0.53      (![X0 : $i]: ((X0) = (k2_struct_0 @ (g1_pre_topc @ X0 @ k1_xboole_0)))),
% 0.38/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.53  thf('47', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.53  thf(fc12_struct_0, axiom,
% 0.38/0.53    (![A:$i]:
% 0.38/0.53     ( ( l1_struct_0 @ A ) =>
% 0.38/0.53       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.53  thf('48', plain,
% 0.38/0.53      (![X23 : $i]:
% 0.38/0.53         (~ (v1_subset_1 @ (k2_struct_0 @ X23) @ (u1_struct_0 @ X23))
% 0.38/0.53          | ~ (l1_struct_0 @ X23))),
% 0.38/0.53      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.38/0.53  thf('49', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.53          | ~ (l1_pre_topc @ X0)
% 0.38/0.53          | ~ (l1_struct_0 @ X0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.53  thf('50', plain,
% 0.38/0.53      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.53  thf('51', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (~ (l1_pre_topc @ X0)
% 0.38/0.53          | ~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.38/0.53      inference('clc', [status(thm)], ['49', '50'])).
% 0.38/0.53  thf('52', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (~ (v1_subset_1 @ (k2_struct_0 @ (g1_pre_topc @ X0 @ k1_xboole_0)) @ 
% 0.38/0.53             X0)
% 0.38/0.53          | ~ (l1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['46', '51'])).
% 0.38/0.53  thf('53', plain,
% 0.38/0.53      (![X0 : $i]: ((X0) = (k2_struct_0 @ (g1_pre_topc @ X0 @ k1_xboole_0)))),
% 0.38/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.53  thf('54', plain,
% 0.38/0.53      (![X0 : $i]: (l1_pre_topc @ (g1_pre_topc @ X0 @ k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.53  thf('55', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.38/0.53      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.38/0.53  thf('56', plain, ($false), inference('sup-', [status(thm)], ['27', '55'])).
% 0.38/0.53  
% 0.38/0.53  % SZS output end Refutation
% 0.38/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
