%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDn6V1Lgag

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:45 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 115 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  420 (1597 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('33',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['24','31','32'])).

thf('34',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDn6V1Lgag
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 400 iterations in 0.258s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.71  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.47/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.47/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.47/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.71  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(t42_tex_2, conjecture,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( v2_tex_2 @ B @ A ) =>
% 0.47/0.71             ( ![C:$i]:
% 0.47/0.71               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.71                 ( ( r2_hidden @ C @ B ) =>
% 0.47/0.71                   ( ( k9_subset_1 @
% 0.47/0.71                       ( u1_struct_0 @ A ) @ B @ 
% 0.47/0.71                       ( k2_pre_topc @
% 0.47/0.71                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.47/0.71                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i]:
% 0.47/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.71            ( l1_pre_topc @ A ) ) =>
% 0.47/0.71          ( ![B:$i]:
% 0.47/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71              ( ( v2_tex_2 @ B @ A ) =>
% 0.47/0.71                ( ![C:$i]:
% 0.47/0.71                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.71                    ( ( r2_hidden @ C @ B ) =>
% 0.47/0.71                      ( ( k9_subset_1 @
% 0.47/0.71                          ( u1_struct_0 @ A ) @ B @ 
% 0.47/0.71                          ( k2_pre_topc @
% 0.47/0.71                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.47/0.71                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.47/0.71  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t3_subset, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (![X14 : $i, X15 : $i]:
% 0.47/0.71         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('4', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.71  thf(d3_tarski, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.71  thf('5', plain,
% 0.47/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.47/0.71          | (r2_hidden @ X3 @ X5)
% 0.47/0.71          | ~ (r1_tarski @ X4 @ X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.71  thf('7', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.47/0.71  thf(l1_zfmisc_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.71  thf('8', plain,
% 0.47/0.71      (![X11 : $i, X13 : $i]:
% 0.47/0.71         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.71  thf('9', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X14 : $i, X16 : $i]:
% 0.47/0.71         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.47/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t41_tex_2, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( v2_tex_2 @ B @ A ) <=>
% 0.47/0.71             ( ![C:$i]:
% 0.47/0.71               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71                 ( ( r1_tarski @ C @ B ) =>
% 0.47/0.71                   ( ( k9_subset_1 @
% 0.47/0.71                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.47/0.71                     ( C ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf('13', plain,
% 0.47/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71          | ~ (v2_tex_2 @ X19 @ X20)
% 0.47/0.71          | ~ (r1_tarski @ X21 @ X19)
% 0.47/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.47/0.71              (k2_pre_topc @ X20 @ X21)) = (X21))
% 0.47/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.47/0.71          | ~ (l1_pre_topc @ X20)
% 0.47/0.71          | ~ (v2_pre_topc @ X20)
% 0.47/0.71          | (v2_struct_0 @ X20))),
% 0.47/0.71      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.71          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.47/0.71          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.47/0.71          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('17', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_A)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.71          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.47/0.71          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.47/0.71      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.47/0.71  thf('19', plain,
% 0.47/0.71      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.47/0.71        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.47/0.71        | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['11', '18'])).
% 0.47/0.71  thf('20', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('21', plain,
% 0.47/0.71      (![X11 : $i, X13 : $i]:
% 0.47/0.71         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.71  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.47/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.47/0.71        | (v2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['19', '22'])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.47/0.71         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('25', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(redefinition_k6_domain_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.47/0.71       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      (![X17 : $i, X18 : $i]:
% 0.47/0.71         ((v1_xboole_0 @ X17)
% 0.47/0.71          | ~ (m1_subset_1 @ X18 @ X17)
% 0.47/0.71          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.47/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.71  thf('28', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.47/0.71  thf(d1_xboole_0, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.71  thf('29', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.71  thf('30', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.71  thf('31', plain,
% 0.47/0.71      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.47/0.71      inference('clc', [status(thm)], ['27', '30'])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.47/0.71      inference('clc', [status(thm)], ['27', '30'])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.47/0.71         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.47/0.71      inference('demod', [status(thm)], ['24', '31', '32'])).
% 0.47/0.71  thf('34', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.71      inference('simplify_reflect-', [status(thm)], ['23', '33'])).
% 0.47/0.71  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
