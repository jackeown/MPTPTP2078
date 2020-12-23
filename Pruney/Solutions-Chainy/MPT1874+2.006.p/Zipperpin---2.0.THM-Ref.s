%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYEdoLL6ft

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:42 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 109 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  447 (1549 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('37',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['24','35','36'])).

thf('38',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jYEdoLL6ft
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 259 iterations in 0.127s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(t42_tex_2, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v2_tex_2 @ B @ A ) =>
% 0.40/0.58             ( ![C:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                 ( ( r2_hidden @ C @ B ) =>
% 0.40/0.58                   ( ( k9_subset_1 @
% 0.40/0.58                       ( u1_struct_0 @ A ) @ B @ 
% 0.40/0.58                       ( k2_pre_topc @
% 0.40/0.58                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.40/0.58                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58            ( l1_pre_topc @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58              ( ( v2_tex_2 @ B @ A ) =>
% 0.40/0.58                ( ![C:$i]:
% 0.40/0.58                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                    ( ( r2_hidden @ C @ B ) =>
% 0.40/0.58                      ( ( k9_subset_1 @
% 0.40/0.58                          ( u1_struct_0 @ A ) @ B @ 
% 0.40/0.58                          ( k2_pre_topc @
% 0.40/0.58                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.40/0.58                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.40/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t3_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i]:
% 0.40/0.58         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('4', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf(d3_tarski, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.40/0.58          | (r2_hidden @ X3 @ X5)
% 0.40/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('7', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '6'])).
% 0.40/0.58  thf(l1_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X10 : $i, X12 : $i]:
% 0.40/0.58         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.58  thf('9', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X15 : $i, X17 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t41_tex_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v2_tex_2 @ B @ A ) <=>
% 0.40/0.58             ( ![C:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58                 ( ( r1_tarski @ C @ B ) =>
% 0.40/0.58                   ( ( k9_subset_1 @
% 0.40/0.58                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.40/0.58                     ( C ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.58          | ~ (v2_tex_2 @ X20 @ X21)
% 0.40/0.58          | ~ (r1_tarski @ X22 @ X20)
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.40/0.58              (k2_pre_topc @ X21 @ X22)) = (X22))
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21)
% 0.40/0.58          | (v2_struct_0 @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.40/0.58          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('17', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.40/0.58        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '18'])).
% 0.40/0.58  thf('20', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X10 : $i, X12 : $i]:
% 0.40/0.58         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.58  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.40/0.58         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('25', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X18)
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ X18)
% 0.40/0.58          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.40/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc1_subset_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.40/0.58          | (v1_xboole_0 @ X13)
% 0.40/0.58          | ~ (v1_xboole_0 @ X14))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d1_xboole_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.58  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('clc', [status(thm)], ['30', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.40/0.58      inference('clc', [status(thm)], ['27', '34'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.40/0.58      inference('clc', [status(thm)], ['27', '34'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.40/0.58         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.40/0.58      inference('demod', [status(thm)], ['24', '35', '36'])).
% 0.40/0.58  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['23', '37'])).
% 0.40/0.58  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
