%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jGecubEpul

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 128 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  601 (1869 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X14 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ ( k2_pre_topc @ X24 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X8 @ X10 @ X9 )
        = ( k9_subset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B )
    | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ sk_B )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ sk_B )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ sk_B )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('31',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ sk_B )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_C_2 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_C_2 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('42',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('48',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jGecubEpul
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 233 iterations in 0.113s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.57  thf(t42_tex_2, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.57           ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.57             ( ![C:$i]:
% 0.22/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.57                 ( ( r2_hidden @ C @ B ) =>
% 0.22/0.57                   ( ( k9_subset_1 @
% 0.22/0.57                       ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.57                       ( k2_pre_topc @
% 0.22/0.57                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.22/0.57                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.57            ( l1_pre_topc @ A ) ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.57              ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.57                ( ![C:$i]:
% 0.22/0.57                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.57                    ( ( r2_hidden @ C @ B ) =>
% 0.22/0.57                      ( ( k9_subset_1 @
% 0.22/0.57                          ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.57                          ( k2_pre_topc @
% 0.22/0.57                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.22/0.57                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.22/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d3_struct_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X18 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t2_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((r2_hidden @ X16 @ X17)
% 0.22/0.57          | (v1_xboole_0 @ X17)
% 0.22/0.57          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf(t63_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.57       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         ((m1_subset_1 @ (k1_tarski @ X14) @ (k1_zfmisc_1 @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X14 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.22/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t41_tex_2, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.22/0.57             ( ![C:$i]:
% 0.22/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.57                 ( ( r1_tarski @ C @ B ) =>
% 0.22/0.57                   ( ( k9_subset_1 @
% 0.22/0.57                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.22/0.57                     ( C ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.57          | ~ (v2_tex_2 @ X23 @ X24)
% 0.22/0.57          | ~ (r1_tarski @ X25 @ X23)
% 0.22/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ 
% 0.22/0.57              (k2_pre_topc @ X24 @ X25)) = (X25))
% 0.22/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.57          | ~ (l1_pre_topc @ X24)
% 0.22/0.57          | ~ (v2_pre_topc @ X24)
% 0.22/0.57          | (v2_struct_0 @ X24))),
% 0.22/0.57      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v2_struct_0 @ sk_A)
% 0.22/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.57              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('12', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v2_struct_0 @ sk_A)
% 0.22/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.57              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.57          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(commutativity_k9_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 0.22/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.57           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.57         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.22/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.57           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X0 @ sk_B)
% 0.22/0.57           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v2_struct_0 @ sk_A)
% 0.22/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.57          | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_B) = (X0))
% 0.22/0.57          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '20'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)
% 0.22/0.57        | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ sk_B)
% 0.22/0.57            = (k1_tarski @ sk_C_2))
% 0.22/0.57        | (v2_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '21'])).
% 0.22/0.57  thf('23', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(l1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X5 : $i, X7 : $i]:
% 0.22/0.57         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.22/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.57  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ sk_B)
% 0.22/0.57            = (k1_tarski @ sk_C_2))
% 0.22/0.57        | (v2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['22', '25'])).
% 0.22/0.57  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ sk_B)
% 0.22/0.57          = (k1_tarski @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.57  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i]:
% 0.22/0.57         ((v1_xboole_0 @ X21)
% 0.22/0.57          | ~ (m1_subset_1 @ X22 @ X21)
% 0.22/0.57          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.57         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.22/0.57         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.57          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.22/0.57          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k3_xboole_0 @ X0 @ sk_B)
% 0.22/0.57           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ sk_B)
% 0.22/0.57          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      ((((k1_tarski @ sk_C_2) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['28', '35'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | ((k1_tarski @ sk_C_2)
% 0.22/0.57            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('39', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['1', '39'])).
% 0.22/0.57  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_l1_pre_topc, axiom,
% 0.22/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.57  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.57  thf('44', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['40', '43'])).
% 0.22/0.57  thf(fc5_struct_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.57       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X20 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X20))
% 0.22/0.57          | ~ (l1_struct_0 @ X20)
% 0.22/0.57          | (v2_struct_0 @ X20))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.57  thf('46', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.57  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.57  thf('48', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.57  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
