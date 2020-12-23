%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gYEt1SgZYQ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  91 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 (1331 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( k2_pre_topc @ X13 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

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
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','26'])).

thf('28',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gYEt1SgZYQ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 36 iterations in 0.019s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.44  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.44  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.44  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(t42_tex_2, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.44             ( ![C:$i]:
% 0.20/0.44               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.44                 ( ( r2_hidden @ C @ B ) =>
% 0.20/0.44                   ( ( k9_subset_1 @
% 0.20/0.44                       ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.44                       ( k2_pre_topc @
% 0.20/0.44                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.44                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.44            ( l1_pre_topc @ A ) ) =>
% 0.20/0.44          ( ![B:$i]:
% 0.20/0.44            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44              ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.44                ( ![C:$i]:
% 0.20/0.44                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.44                    ( ( r2_hidden @ C @ B ) =>
% 0.20/0.44                      ( ( k9_subset_1 @
% 0.20/0.44                          ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.44                          ( k2_pre_topc @
% 0.20/0.44                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.44                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.20/0.44  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.44       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i]:
% 0.20/0.44         ((v1_xboole_0 @ X10)
% 0.20/0.44          | ~ (m1_subset_1 @ X11 @ X10)
% 0.20/0.44          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.44        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.20/0.44         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.20/0.44          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.20/0.44        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf('6', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(l3_subset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.44          | (r2_hidden @ X3 @ X5)
% 0.20/0.44          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.44      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.44  thf(t63_subset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.44       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]:
% 0.20/0.44         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.20/0.44          | ~ (r2_hidden @ X6 @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.44        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t41_tex_2, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.44             ( ![C:$i]:
% 0.20/0.44               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44                 ( ( r1_tarski @ C @ B ) =>
% 0.20/0.44                   ( ( k9_subset_1 @
% 0.20/0.44                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.20/0.44                     ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.44          | ~ (v2_tex_2 @ X12 @ X13)
% 0.20/0.44          | ~ (r1_tarski @ X14 @ X12)
% 0.20/0.44          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.20/0.44              (k2_pre_topc @ X13 @ X14)) = (X14))
% 0.20/0.44          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.44          | ~ (l1_pre_topc @ X13)
% 0.20/0.44          | ~ (v2_pre_topc @ X13)
% 0.20/0.44          | (v2_struct_0 @ X13))),
% 0.20/0.44      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((v2_struct_0 @ sk_A)
% 0.20/0.44          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.44          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.44          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.44          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.44          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.44  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('18', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((v2_struct_0 @ sk_A)
% 0.20/0.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.44          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.44          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.20/0.44  thf('20', plain,
% 0.20/0.44      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.20/0.44        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.20/0.44        | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '19'])).
% 0.20/0.44  thf('21', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(l1_zfmisc_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.44  thf('22', plain,
% 0.20/0.44      (![X0 : $i, X2 : $i]:
% 0.20/0.44         ((r1_tarski @ (k1_tarski @ X0) @ X2) | ~ (r2_hidden @ X0 @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.44  thf('23', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.20/0.44        | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.44  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('26', plain,
% 0.20/0.44      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.44         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))),
% 0.20/0.44      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.44  thf('27', plain,
% 0.20/0.44      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.20/0.44        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('demod', [status(thm)], ['5', '26'])).
% 0.20/0.44  thf('28', plain,
% 0.20/0.44      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.44        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf('29', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.44  thf(fc2_struct_0, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.44  thf('30', plain,
% 0.20/0.44      (![X9 : $i]:
% 0.20/0.44         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.20/0.44          | ~ (l1_struct_0 @ X9)
% 0.20/0.44          | (v2_struct_0 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.44  thf('31', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.44  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(dt_l1_pre_topc, axiom,
% 0.20/0.44    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.44  thf('33', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.44  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.44  thf('35', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.44  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
