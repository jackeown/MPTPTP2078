%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESSXy063lN

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:47 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  426 (1228 expanded)
%              Number of equality atoms :   13 (  35 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 @ ( k2_pre_topc @ X11 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('34',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESSXy063lN
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 75 iterations in 0.053s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(t42_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v2_tex_2 @ B @ A ) =>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56                 ( ( r2_hidden @ C @ B ) =>
% 0.37/0.56                   ( ( k9_subset_1 @
% 0.37/0.56                       ( u1_struct_0 @ A ) @ B @ 
% 0.37/0.56                       ( k2_pre_topc @
% 0.37/0.56                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.37/0.56                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.40/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56              ( ( v2_tex_2 @ B @ A ) =>
% 0.40/0.56                ( ![C:$i]:
% 0.40/0.56                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.56                    ( ( r2_hidden @ C @ B ) =>
% 0.40/0.56                      ( ( k9_subset_1 @
% 0.40/0.56                          ( u1_struct_0 @ A ) @ B @ 
% 0.40/0.56                          ( k2_pre_topc @
% 0.40/0.56                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.40/0.56                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.40/0.56    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.40/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(d3_struct_0, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.56  thf('1', plain,
% 0.40/0.56      (![X3 : $i]:
% 0.40/0.56         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.40/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.56  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.40/0.56  thf('3', plain,
% 0.40/0.56      (![X8 : $i, X9 : $i]:
% 0.40/0.56         ((v1_xboole_0 @ X8)
% 0.40/0.56          | ~ (m1_subset_1 @ X9 @ X8)
% 0.40/0.56          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.40/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.40/0.56  thf('4', plain,
% 0.40/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.56  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(dt_k6_domain_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.56  thf('6', plain,
% 0.40/0.56      (![X6 : $i, X7 : $i]:
% 0.40/0.56         ((v1_xboole_0 @ X6)
% 0.40/0.56          | ~ (m1_subset_1 @ X7 @ X6)
% 0.40/0.56          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.40/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.40/0.56  thf('7', plain,
% 0.40/0.56      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.40/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.56  thf('8', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(t41_tex_2, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.40/0.56             ( ![C:$i]:
% 0.40/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56                 ( ( r1_tarski @ C @ B ) =>
% 0.40/0.56                   ( ( k9_subset_1 @
% 0.40/0.56                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.40/0.56                     ( C ) ) ) ) ) ) ) ) ))).
% 0.40/0.56  thf('9', plain,
% 0.40/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.40/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.40/0.56          | ~ (r1_tarski @ X12 @ X10)
% 0.40/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X11) @ X10 @ 
% 0.40/0.56              (k2_pre_topc @ X11 @ X12)) = (X12))
% 0.40/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.40/0.56          | ~ (l1_pre_topc @ X11)
% 0.40/0.56          | ~ (v2_pre_topc @ X11)
% 0.40/0.56          | (v2_struct_0 @ X11))),
% 0.40/0.56      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.40/0.56  thf('10', plain,
% 0.40/0.56      (![X0 : $i]:
% 0.40/0.56         ((v2_struct_0 @ sk_A)
% 0.40/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.40/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.40/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.56  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('13', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('14', plain,
% 0.40/0.56      (![X0 : $i]:
% 0.40/0.56         ((v2_struct_0 @ sk_A)
% 0.40/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.40/0.56          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.40/0.56      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.40/0.56  thf('15', plain,
% 0.40/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.56        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.40/0.56        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.56            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.40/0.56            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.40/0.56        | (v2_struct_0 @ sk_A))),
% 0.40/0.56      inference('sup-', [status(thm)], ['7', '14'])).
% 0.40/0.56  thf('16', plain,
% 0.40/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.56         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.40/0.56         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('17', plain,
% 0.40/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.56        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.40/0.56        | (v2_struct_0 @ sk_A))),
% 0.40/0.56      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.40/0.56  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('19', plain,
% 0.40/0.56      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.40/0.56  thf('20', plain,
% 0.40/0.56      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['4', '19'])).
% 0.40/0.56  thf('21', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(l1_zfmisc_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.56  thf('22', plain,
% 0.40/0.56      (![X0 : $i, X2 : $i]:
% 0.40/0.56         ((r1_tarski @ (k1_tarski @ X0) @ X2) | ~ (r2_hidden @ X0 @ X2))),
% 0.40/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.56  thf('23', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.40/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.56  thf('24', plain,
% 0.40/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.40/0.56  thf('25', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.40/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.56  thf('26', plain,
% 0.40/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.56      inference('sup+', [status(thm)], ['1', '25'])).
% 0.40/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(dt_l1_pre_topc, axiom,
% 0.40/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.56  thf('28', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.40/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.56  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.56  thf('30', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.40/0.56      inference('demod', [status(thm)], ['26', '29'])).
% 0.40/0.56  thf(fc5_struct_0, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.56       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.40/0.56  thf('31', plain,
% 0.40/0.56      (![X5 : $i]:
% 0.40/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X5))
% 0.40/0.56          | ~ (l1_struct_0 @ X5)
% 0.40/0.56          | (v2_struct_0 @ X5))),
% 0.40/0.56      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.40/0.56  thf('32', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.56  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.56  thf('34', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.56  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.40/0.56  
% 0.40/0.56  % SZS output end Refutation
% 0.40/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
