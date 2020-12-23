%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IuAu0DGcy9

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 110 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  538 (1418 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ ( k2_pre_topc @ X19 @ X20 ) ) )
        = ( k2_pre_topc @ X19 @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','15','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('41',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','28','39','40'])).

thf('42',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('44',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IuAu0DGcy9
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 83 iterations in 0.035s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.46  thf(d3_struct_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X14 : $i]:
% 0.20/0.46         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.46  thf(t81_tops_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( v1_tops_1 @ B @ A ) =>
% 0.20/0.46             ( ![C:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                 ( ( v3_pre_topc @ C @ A ) =>
% 0.20/0.46                   ( ( k2_pre_topc @ A @ C ) =
% 0.20/0.46                     ( k2_pre_topc @
% 0.20/0.46                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46              ( ( v1_tops_1 @ B @ A ) =>
% 0.20/0.46                ( ![C:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                    ( ( v3_pre_topc @ C @ A ) =>
% 0.20/0.46                      ( ( k2_pre_topc @ A @ C ) =
% 0.20/0.46                        ( k2_pre_topc @
% 0.20/0.46                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t41_tops_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.46                 ( ( k2_pre_topc @
% 0.20/0.46                     A @ 
% 0.20/0.46                     ( k9_subset_1 @
% 0.20/0.46                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.20/0.46                   ( k2_pre_topc @
% 0.20/0.46                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.46          | ~ (v3_pre_topc @ X18 @ X19)
% 0.20/0.46          | ((k2_pre_topc @ X19 @ 
% 0.20/0.46              (k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 0.20/0.46               (k2_pre_topc @ X19 @ X20)))
% 0.20/0.46              = (k2_pre_topc @ X19 @ 
% 0.20/0.46                 (k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20)))
% 0.20/0.46          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.46          | ~ (l1_pre_topc @ X19)
% 0.20/0.46          | ~ (v2_pre_topc @ X19))),
% 0.20/0.46      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v2_pre_topc @ sk_A)
% 0.20/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.46               (k2_pre_topc @ sk_A @ X0)))
% 0.20/0.46              = (k2_pre_topc @ sk_A @ 
% 0.20/0.46                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 0.20/0.46          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | ((k2_pre_topc @ sk_A @ 
% 0.20/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.46               (k2_pre_topc @ sk_A @ X0)))
% 0.20/0.46              = (k2_pre_topc @ sk_A @ 
% 0.20/0.46                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((k2_pre_topc @ sk_A @ 
% 0.20/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.46          (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.46         = (k2_pre_topc @ sk_A @ 
% 0.20/0.46            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d3_tops_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.46             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X16 : $i, X17 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.46          | ~ (v1_tops_1 @ X16 @ X17)
% 0.20/0.46          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.20/0.46          | ~ (l1_pre_topc @ X17))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.20/0.46        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.46         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.20/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.46           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (((k2_pre_topc @ sk_A @ 
% 0.20/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.20/0.46         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      ((((k2_pre_topc @ sk_A @ 
% 0.20/0.46          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.20/0.46          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))
% 0.20/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '19'])).
% 0.20/0.46  thf(d3_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X11 : $i, X13 : $i]:
% 0.20/0.46         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.46         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.20/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X14 : $i]:
% 0.20/0.46         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.20/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_l1_pre_topc, axiom,
% 0.20/0.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.46  thf('33', plain,
% 0.20/0.47      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('37', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf(t28_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (sk_C_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.20/0.47         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '28', '39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.20/0.47         != (k2_pre_topc @ sk_A @ 
% 0.20/0.47             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.47           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.20/0.47         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
