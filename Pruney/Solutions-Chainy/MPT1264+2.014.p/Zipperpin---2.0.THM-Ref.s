%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zlXz4Lg2Ma

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  572 (1445 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) ) )
        = ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
      = sk_C_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('43',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25','41','42'])).

thf('44',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('46',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zlXz4Lg2Ma
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 98 iterations in 0.055s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X16 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf(t81_tops_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v1_tops_1 @ B @ A ) =>
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                 ( ( v3_pre_topc @ C @ A ) =>
% 0.21/0.51                   ( ( k2_pre_topc @ A @ C ) =
% 0.21/0.51                     ( k2_pre_topc @
% 0.21/0.51                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ( v1_tops_1 @ B @ A ) =>
% 0.21/0.51                ( ![C:$i]:
% 0.21/0.51                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                    ( ( v3_pre_topc @ C @ A ) =>
% 0.21/0.51                      ( ( k2_pre_topc @ A @ C ) =
% 0.21/0.51                        ( k2_pre_topc @
% 0.21/0.51                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t41_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.51                 ( ( k2_pre_topc @
% 0.21/0.51                     A @ 
% 0.21/0.51                     ( k9_subset_1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.21/0.51                   ( k2_pre_topc @
% 0.21/0.51                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (v3_pre_topc @ X20 @ X21)
% 0.21/0.51          | ((k2_pre_topc @ X21 @ 
% 0.21/0.51              (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.21/0.51               (k2_pre_topc @ X21 @ X22)))
% 0.21/0.51              = (k2_pre_topc @ X21 @ 
% 0.21/0.51                 (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22)))
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (l1_pre_topc @ X21)
% 0.21/0.51          | ~ (v2_pre_topc @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ((k2_pre_topc @ sk_A @ 
% 0.21/0.51              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.21/0.51               (k2_pre_topc @ sk_A @ X0)))
% 0.21/0.51              = (k2_pre_topc @ sk_A @ 
% 0.21/0.51                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 0.21/0.51          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ((k2_pre_topc @ sk_A @ 
% 0.21/0.51              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.21/0.51               (k2_pre_topc @ sk_A @ X0)))
% 0.21/0.51              = (k2_pre_topc @ sk_A @ 
% 0.21/0.51                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ 
% 0.21/0.51         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.21/0.51          (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.51         = (k2_pre_topc @ sk_A @ 
% 0.21/0.51            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.51             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.51          | ~ (v1_tops_1 @ X18 @ X19)
% 0.21/0.51          | ((k2_pre_topc @ X19 @ X18) = (k2_struct_0 @ X19))
% 0.21/0.51          | ~ (l1_pre_topc @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.51           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ 
% 0.21/0.51         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.51         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ 
% 0.21/0.51          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.51          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '19'])).
% 0.21/0.51  thf(dt_k2_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.51  thf('22', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('23', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X16 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.51          | (r2_hidden @ X8 @ X10)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_C_1 @ X0)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)) = (sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((((k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (sk_C_1))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '36'])).
% 0.21/0.51  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '40'])).
% 0.21/0.51  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.21/0.51         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '25', '41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.21/0.51         != (k2_pre_topc @ sk_A @ 
% 0.21/0.51             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.51           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.21/0.51         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
