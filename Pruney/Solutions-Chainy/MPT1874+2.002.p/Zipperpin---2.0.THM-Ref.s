%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c6KmACfA5I

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:41 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 116 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  436 (1645 expanded)
%              Number of equality atoms :   15 (  48 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','10'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X14 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ~ ( r1_tarski @ X30 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_pre_topc @ X29 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X14 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('31',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('33',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('35',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['28','33','34'])).

thf('36',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['27','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c6KmACfA5I
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:57:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.16  % Solved by: fo/fo7.sh
% 0.91/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.16  % done 1342 iterations in 0.704s
% 0.91/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.16  % SZS output start Refutation
% 0.91/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.16  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.91/1.16  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.91/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.16  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.91/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.16  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.91/1.16  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.16  thf(t42_tex_2, conjecture,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.16           ( ( v2_tex_2 @ B @ A ) =>
% 0.91/1.16             ( ![C:$i]:
% 0.91/1.16               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.16                 ( ( r2_hidden @ C @ B ) =>
% 0.91/1.16                   ( ( k9_subset_1 @
% 0.91/1.16                       ( u1_struct_0 @ A ) @ B @ 
% 0.91/1.16                       ( k2_pre_topc @
% 0.91/1.16                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.91/1.16                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.91/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.16    (~( ![A:$i]:
% 0.91/1.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.16            ( l1_pre_topc @ A ) ) =>
% 0.91/1.16          ( ![B:$i]:
% 0.91/1.16            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.16              ( ( v2_tex_2 @ B @ A ) =>
% 0.91/1.16                ( ![C:$i]:
% 0.91/1.16                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.16                    ( ( r2_hidden @ C @ B ) =>
% 0.91/1.16                      ( ( k9_subset_1 @
% 0.91/1.16                          ( u1_struct_0 @ A ) @ B @ 
% 0.91/1.16                          ( k2_pre_topc @
% 0.91/1.16                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.91/1.16                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.91/1.16    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.91/1.16  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(t2_subset, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( m1_subset_1 @ A @ B ) =>
% 0.91/1.16       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.91/1.16  thf('2', plain,
% 0.91/1.16      (![X18 : $i, X19 : $i]:
% 0.91/1.16         ((r2_hidden @ X18 @ X19)
% 0.91/1.16          | (v1_xboole_0 @ X19)
% 0.91/1.16          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.91/1.16      inference('cnf', [status(esa)], [t2_subset])).
% 0.91/1.16  thf('3', plain,
% 0.91/1.16      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.91/1.16        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.16  thf('4', plain,
% 0.91/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(cc1_subset_1, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( v1_xboole_0 @ A ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.91/1.16  thf('5', plain,
% 0.91/1.16      (![X16 : $i, X17 : $i]:
% 0.91/1.16         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.91/1.16          | (v1_xboole_0 @ X16)
% 0.91/1.16          | ~ (v1_xboole_0 @ X17))),
% 0.91/1.16      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.91/1.16  thf('6', plain,
% 0.91/1.16      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.16  thf('7', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(d1_xboole_0, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.16  thf('8', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.16  thf('9', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.91/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.16  thf('10', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.91/1.16      inference('clc', [status(thm)], ['6', '9'])).
% 0.91/1.16  thf('11', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.91/1.16      inference('clc', [status(thm)], ['3', '10'])).
% 0.91/1.16  thf(t63_subset_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( r2_hidden @ A @ B ) =>
% 0.91/1.16       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.91/1.16  thf('12', plain,
% 0.91/1.16      (![X14 : $i, X15 : $i]:
% 0.91/1.16         ((m1_subset_1 @ (k1_tarski @ X14) @ (k1_zfmisc_1 @ X15))
% 0.91/1.16          | ~ (r2_hidden @ X14 @ X15))),
% 0.91/1.16      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.91/1.16  thf('13', plain,
% 0.91/1.16      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.91/1.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.16  thf('14', plain,
% 0.91/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(t41_tex_2, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.16       ( ![B:$i]:
% 0.91/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.16           ( ( v2_tex_2 @ B @ A ) <=>
% 0.91/1.16             ( ![C:$i]:
% 0.91/1.16               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.16                 ( ( r1_tarski @ C @ B ) =>
% 0.91/1.16                   ( ( k9_subset_1 @
% 0.91/1.16                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.91/1.16                     ( C ) ) ) ) ) ) ) ) ))).
% 0.91/1.16  thf('15', plain,
% 0.91/1.16      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.16         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.91/1.16          | ~ (v2_tex_2 @ X28 @ X29)
% 0.91/1.16          | ~ (r1_tarski @ X30 @ X28)
% 0.91/1.16          | ((k9_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 0.91/1.16              (k2_pre_topc @ X29 @ X30)) = (X30))
% 0.91/1.16          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.91/1.16          | ~ (l1_pre_topc @ X29)
% 0.91/1.16          | ~ (v2_pre_topc @ X29)
% 0.91/1.16          | (v2_struct_0 @ X29))),
% 0.91/1.16      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.91/1.16  thf('16', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         ((v2_struct_0 @ sk_A)
% 0.91/1.16          | ~ (v2_pre_topc @ sk_A)
% 0.91/1.16          | ~ (l1_pre_topc @ sk_A)
% 0.91/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.16          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.91/1.16          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.91/1.16          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.16  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('19', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('20', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         ((v2_struct_0 @ sk_A)
% 0.91/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.16          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.91/1.16          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.91/1.16      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.91/1.16  thf('21', plain,
% 0.91/1.16      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.91/1.16        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.91/1.16        | (v2_struct_0 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['13', '20'])).
% 0.91/1.16  thf('22', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('23', plain,
% 0.91/1.16      (![X14 : $i, X15 : $i]:
% 0.91/1.16         ((m1_subset_1 @ (k1_tarski @ X14) @ (k1_zfmisc_1 @ X15))
% 0.91/1.16          | ~ (r2_hidden @ X14 @ X15))),
% 0.91/1.16      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.91/1.16  thf('24', plain,
% 0.91/1.16      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.16  thf(t3_subset, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.16  thf('25', plain,
% 0.91/1.16      (![X20 : $i, X21 : $i]:
% 0.91/1.16         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.91/1.16      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.16  thf('26', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.91/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.16  thf('27', plain,
% 0.91/1.16      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.91/1.16        | (v2_struct_0 @ sk_A))),
% 0.91/1.16      inference('demod', [status(thm)], ['21', '26'])).
% 0.91/1.16  thf('28', plain,
% 0.91/1.16      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.91/1.16         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf(redefinition_k6_domain_1, axiom,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.91/1.16       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.91/1.16  thf('30', plain,
% 0.91/1.16      (![X26 : $i, X27 : $i]:
% 0.91/1.16         ((v1_xboole_0 @ X26)
% 0.91/1.16          | ~ (m1_subset_1 @ X27 @ X26)
% 0.91/1.16          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.91/1.16      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.91/1.16  thf('31', plain,
% 0.91/1.16      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.91/1.16        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.16  thf('32', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.91/1.16      inference('clc', [status(thm)], ['6', '9'])).
% 0.91/1.16  thf('33', plain,
% 0.91/1.16      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.91/1.16      inference('clc', [status(thm)], ['31', '32'])).
% 0.91/1.16  thf('34', plain,
% 0.91/1.16      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.91/1.16      inference('clc', [status(thm)], ['31', '32'])).
% 0.91/1.16  thf('35', plain,
% 0.91/1.16      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.91/1.16         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.91/1.16      inference('demod', [status(thm)], ['28', '33', '34'])).
% 0.91/1.16  thf('36', plain, ((v2_struct_0 @ sk_A)),
% 0.91/1.16      inference('simplify_reflect-', [status(thm)], ['27', '35'])).
% 0.91/1.16  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.91/1.16  
% 0.91/1.16  % SZS output end Refutation
% 0.91/1.16  
% 0.91/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
