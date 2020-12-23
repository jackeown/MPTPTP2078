%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JuEwwftTX5

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 109 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 (1553 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_pre_topc @ X18 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','22'])).

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
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JuEwwftTX5
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 157 iterations in 0.116s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(t42_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                 ( ( r2_hidden @ C @ B ) =>
% 0.39/0.57                   ( ( k9_subset_1 @
% 0.39/0.57                       ( u1_struct_0 @ A ) @ B @ 
% 0.39/0.57                       ( k2_pre_topc @
% 0.39/0.57                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.39/0.57                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57              ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.57                ( ![C:$i]:
% 0.39/0.57                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                    ( ( r2_hidden @ C @ B ) =>
% 0.39/0.57                      ( ( k9_subset_1 @
% 0.39/0.57                          ( u1_struct_0 @ A ) @ B @ 
% 0.39/0.57                          ( k2_pre_topc @
% 0.39/0.57                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.39/0.57                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.39/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t3_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('4', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.57          | (r2_hidden @ X3 @ X5)
% 0.39/0.57          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '6'])).
% 0.39/0.57  thf(t63_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.39/0.57          | ~ (r2_hidden @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t41_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                 ( ( r1_tarski @ C @ B ) =>
% 0.39/0.57                   ( ( k9_subset_1 @
% 0.39/0.57                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.39/0.57                     ( C ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.57          | ~ (v2_tex_2 @ X17 @ X18)
% 0.39/0.57          | ~ (r1_tarski @ X19 @ X17)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 0.39/0.57              (k2_pre_topc @ X18 @ X19)) = (X19))
% 0.39/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.57          | ~ (l1_pre_topc @ X18)
% 0.39/0.57          | ~ (v2_pre_topc @ X18)
% 0.39/0.57          | (v2_struct_0 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.39/0.57          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('15', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.39/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.39/0.57  thf('18', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.39/0.57          | ~ (r2_hidden @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.39/0.57         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('25', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X15)
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ X15)
% 0.39/0.57          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_subset_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.39/0.57          | (v1_xboole_0 @ X10)
% 0.39/0.57          | ~ (v1_xboole_0 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d1_xboole_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.57  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['30', '33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.39/0.57      inference('clc', [status(thm)], ['27', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.39/0.57      inference('clc', [status(thm)], ['27', '34'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.39/0.57         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['24', '35', '36'])).
% 0.39/0.57  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['23', '37'])).
% 0.39/0.57  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
