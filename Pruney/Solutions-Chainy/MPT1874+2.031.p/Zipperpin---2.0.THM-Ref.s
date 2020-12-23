%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J4mfcwubGl

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  528 (1525 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k2_pre_topc @ X17 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['34','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J4mfcwubGl
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 155 iterations in 0.080s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(t42_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                 ( ( r2_hidden @ C @ B ) =>
% 0.20/0.53                   ( ( k9_subset_1 @
% 0.20/0.53                       ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.53                       ( k2_pre_topc @
% 0.20/0.53                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.53                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.53                ( ![C:$i]:
% 0.20/0.53                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                    ( ( r2_hidden @ C @ B ) =>
% 0.20/0.53                      ( ( k9_subset_1 @
% 0.20/0.53                          ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.53                          ( k2_pre_topc @
% 0.20/0.53                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.53                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.20/0.53  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t5_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.53          | ~ (v1_xboole_0 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ X14)
% 0.20/0.53          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k6_domain_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.53          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t41_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                 ( ( r1_tarski @ C @ B ) =>
% 0.20/0.53                   ( ( k9_subset_1 @
% 0.20/0.53                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.20/0.53                     ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | ~ (v2_tex_2 @ X16 @ X17)
% 0.20/0.53          | ~ (r1_tarski @ X18 @ X16)
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.20/0.53              (k2_pre_topc @ X17 @ X18)) = (X18))
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.53              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.53          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.53              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.53          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)
% 0.20/0.53        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.53            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.20/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.53         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.20/0.53         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.53  thf('23', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.53          | (m1_subset_1 @ X3 @ X4)
% 0.20/0.53          | (v1_xboole_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1) | (m1_subset_1 @ sk_C_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.53          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.53        | (m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('31', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '31'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('34', plain, ((r1_tarski @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1) | (m1_subset_1 @ sk_C_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ X14)
% 0.20/0.53          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.53        | ((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.53  thf('39', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('40', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '41'])).
% 0.20/0.53  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '43'])).
% 0.20/0.53  thf('45', plain, ($false), inference('sup-', [status(thm)], ['0', '44'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
