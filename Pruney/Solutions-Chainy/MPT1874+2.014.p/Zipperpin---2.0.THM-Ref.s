%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qOPNP96gQ5

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
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  441 (1537 expanded)
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

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ ( k2_pre_topc @ X19 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

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
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['25','32'])).

thf('34',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['25','32'])).

thf('35',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','33','34'])).

thf('36',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qOPNP96gQ5
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 100 iterations in 0.071s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(t42_tex_2, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.52             ( ![C:$i]:
% 0.19/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52                 ( ( r2_hidden @ C @ B ) =>
% 0.19/0.52                   ( ( k9_subset_1 @
% 0.19/0.52                       ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.52                       ( k2_pre_topc @
% 0.19/0.52                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.52                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.52            ( l1_pre_topc @ A ) ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52              ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.52                ( ![C:$i]:
% 0.19/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52                    ( ( r2_hidden @ C @ B ) =>
% 0.19/0.52                      ( ( k9_subset_1 @
% 0.19/0.52                          ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.52                          ( k2_pre_topc @
% 0.19/0.52                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.52                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.19/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(l3_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.19/0.52          | (r2_hidden @ X6 @ X8)
% 0.19/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.19/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.52  thf(t63_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.52       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.19/0.52          | ~ (r2_hidden @ X9 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t41_tex_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v2_tex_2 @ B @ A ) <=>
% 0.19/0.52             ( ![C:$i]:
% 0.19/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52                 ( ( r1_tarski @ C @ B ) =>
% 0.19/0.52                   ( ( k9_subset_1 @
% 0.19/0.52                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.19/0.52                     ( C ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.52          | ~ (v2_tex_2 @ X18 @ X19)
% 0.19/0.52          | ~ (r1_tarski @ X20 @ X18)
% 0.19/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 0.19/0.52              (k2_pre_topc @ X19 @ X20)) = (X20))
% 0.19/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.52          | ~ (l1_pre_topc @ X19)
% 0.19/0.52          | ~ (v2_pre_topc @ X19)
% 0.19/0.52          | (v2_struct_0 @ X19))),
% 0.19/0.52      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.52          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.19/0.52          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.52  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('13', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.52          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)
% 0.19/0.52        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.52        | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['7', '14'])).
% 0.19/0.52  thf('16', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.19/0.52          | ~ (r2_hidden @ X9 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf(t3_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i]:
% 0.19/0.52         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.52  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.19/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.52        | (v2_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['15', '20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.19/0.52         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('23', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X16)
% 0.19/0.52          | ~ (m1_subset_1 @ X17 @ X16)
% 0.19/0.52          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.19/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc1_subset_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.19/0.52          | (v1_xboole_0 @ X11)
% 0.19/0.52          | ~ (v1_xboole_0 @ X12))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf('29', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_xboole_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf('31', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.52  thf('32', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('clc', [status(thm)], ['28', '31'])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.19/0.52      inference('clc', [status(thm)], ['25', '32'])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.19/0.52      inference('clc', [status(thm)], ['25', '32'])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.19/0.52         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) != (k1_tarski @ sk_C_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['22', '33', '34'])).
% 0.19/0.52  thf('36', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['21', '35'])).
% 0.19/0.52  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
