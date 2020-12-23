%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6MhQu8cxHJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:09 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 121 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  570 (1727 expanded)
%              Number of equality atoms :   28 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) ) )
        = ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
      = sk_C_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','14','22','38','41'])).

thf('43',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('45',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6MhQu8cxHJ
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 239 iterations in 0.133s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(t81_tops_1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v1_tops_1 @ B @ A ) =>
% 0.42/0.62             ( ![C:$i]:
% 0.42/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                 ( ( v3_pre_topc @ C @ A ) =>
% 0.42/0.62                   ( ( k2_pre_topc @ A @ C ) =
% 0.42/0.62                     ( k2_pre_topc @
% 0.42/0.62                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62              ( ( v1_tops_1 @ B @ A ) =>
% 0.42/0.62                ( ![C:$i]:
% 0.42/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                    ( ( v3_pre_topc @ C @ A ) =>
% 0.42/0.62                      ( ( k2_pre_topc @ A @ C ) =
% 0.42/0.62                        ( k2_pre_topc @
% 0.42/0.62                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t41_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62               ( ( v3_pre_topc @ B @ A ) =>
% 0.42/0.62                 ( ( k2_pre_topc @
% 0.42/0.62                     A @ 
% 0.42/0.62                     ( k9_subset_1 @
% 0.42/0.62                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.42/0.62                   ( k2_pre_topc @
% 0.42/0.62                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.62          | ~ (v3_pre_topc @ X20 @ X21)
% 0.42/0.62          | ((k2_pre_topc @ X21 @ 
% 0.42/0.62              (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.42/0.62               (k2_pre_topc @ X21 @ X22)))
% 0.42/0.62              = (k2_pre_topc @ X21 @ 
% 0.42/0.62                 (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22)))
% 0.42/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.62          | ~ (l1_pre_topc @ X21)
% 0.42/0.62          | ~ (v2_pre_topc @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_pre_topc @ sk_A)
% 0.42/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.42/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.42/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.42/0.62              = (k2_pre_topc @ sk_A @ 
% 0.42/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 0.42/0.62          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('6', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.42/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.42/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.42/0.62              = (k2_pre_topc @ sk_A @ 
% 0.42/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ 
% 0.42/0.62         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.42/0.62          (k2_pre_topc @ sk_A @ sk_B)))
% 0.42/0.62         = (k2_pre_topc @ sk_A @ 
% 0.42/0.62            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d3_tops_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( v1_tops_1 @ B @ A ) <=>
% 0.42/0.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.62          | ~ (v1_tops_1 @ X18 @ X19)
% 0.42/0.62          | ((k2_pre_topc @ X19 @ X18) = (k2_struct_0 @ X19))
% 0.42/0.62          | ~ (l1_pre_topc @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.42/0.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('14', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k2_pre_topc, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.42/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @
% 0.42/0.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X15)
% 0.42/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.42/0.62          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.42/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('18', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.42/0.62  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.42/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.42/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (k2_struct_0 @ sk_A))
% 0.42/0.62           = (k3_xboole_0 @ X0 @ (k2_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf(d3_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(l3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X6 @ X7)
% 0.42/0.62          | (r2_hidden @ X6 @ X8)
% 0.42/0.62          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ sk_C_1 @ X0)
% 0.42/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.62  thf(t28_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X4 : $i, X5 : $i]:
% 0.42/0.62         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)) = (sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      ((((k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (sk_C_1))
% 0.42/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['23', '33'])).
% 0.42/0.62  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_l1_pre_topc, axiom,
% 0.42/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.62  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (((k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (sk_C_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['34', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.42/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.42/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.42/0.62         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['8', '14', '22', '38', '41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.42/0.62         != (k2_pre_topc @ sk_A @ 
% 0.42/0.62             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.42/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.42/0.62         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
