%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gtyaSE17DJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 131 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  429 (1926 expanded)
%              Number of equality atoms :   16 (  58 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ ( k2_pre_topc @ X12 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X2 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('32',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('33',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gtyaSE17DJ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 32 iterations in 0.020s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.46  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(t42_tex_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46           ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.46             ( ![C:$i]:
% 0.19/0.46               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.46                 ( ( r2_hidden @ C @ B ) =>
% 0.19/0.46                   ( ( k9_subset_1 @
% 0.19/0.46                       ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.46                       ( k2_pre_topc @
% 0.19/0.46                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.46                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.46            ( l1_pre_topc @ A ) ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46              ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.46                ( ![C:$i]:
% 0.19/0.46                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.46                    ( ( r2_hidden @ C @ B ) =>
% 0.19/0.46                      ( ( k9_subset_1 @
% 0.19/0.46                          ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.46                          ( k2_pre_topc @
% 0.19/0.46                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.46                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.19/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_k6_domain_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.46       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         ((v1_xboole_0 @ X7)
% 0.19/0.46          | ~ (m1_subset_1 @ X8 @ X7)
% 0.19/0.46          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.19/0.46         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.46       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]:
% 0.19/0.46         ((v1_xboole_0 @ X9)
% 0.19/0.46          | ~ (m1_subset_1 @ X10 @ X9)
% 0.19/0.46          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.19/0.46        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc1_subset_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.46          | (v1_xboole_0 @ X5)
% 0.19/0.46          | ~ (v1_xboole_0 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t7_boole, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_boole])).
% 0.19/0.46  thf('12', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('clc', [status(thm)], ['9', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['6', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.19/0.46         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '14'])).
% 0.19/0.46  thf('16', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.46      inference('clc', [status(thm)], ['9', '12'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.19/0.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t41_tex_2, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46           ( ( v2_tex_2 @ B @ A ) <=>
% 0.19/0.46             ( ![C:$i]:
% 0.19/0.46               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46                 ( ( r1_tarski @ C @ B ) =>
% 0.19/0.46                   ( ( k9_subset_1 @
% 0.19/0.46                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.19/0.46                     ( C ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.46          | ~ (v2_tex_2 @ X11 @ X12)
% 0.19/0.46          | ~ (r1_tarski @ X13 @ X11)
% 0.19/0.46          | ((k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ 
% 0.19/0.46              (k2_pre_topc @ X12 @ X13)) = (X13))
% 0.19/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.46          | ~ (l1_pre_topc @ X12)
% 0.19/0.46          | ~ (v2_pre_topc @ X12)
% 0.19/0.46          | (v2_struct_0 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v2_struct_0 @ sk_A)
% 0.19/0.46          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.46          | ~ (r1_tarski @ X0 @ sk_B)
% 0.19/0.46          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('23', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v2_struct_0 @ sk_A)
% 0.19/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.46          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.19/0.46        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.46        | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '24'])).
% 0.19/0.46  thf('26', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t37_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X2 : $i, X4 : $i]:
% 0.19/0.46         ((r1_tarski @ (k1_tarski @ X2) @ X4) | ~ (r2_hidden @ X2 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.19/0.46  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.46        | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['25', '28'])).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.19/0.46         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['6', '13'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['6', '13'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.46         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) != (k1_tarski @ sk_C_1))),
% 0.19/0.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.46  thf('34', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['29', '33'])).
% 0.19/0.46  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
