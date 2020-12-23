%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JnQXi0bS9y

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 184 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  707 (1787 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t79_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( r1_tarski @ B @ C ) )
                 => ( v1_tops_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    r2_hidden @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
       != ( k2_struct_0 @ X23 ) )
      | ( v1_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_C_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C_1 )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_tops_1 @ sk_C_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C_1 )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_tops_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ ( k2_pre_topc @ X20 @ X19 ) @ ( k2_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('57',plain,(
    r2_hidden @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('59',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k2_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['47','72','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','74'])).

thf('76',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['37','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JnQXi0bS9y
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 291 iterations in 0.117s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(d3_struct_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X15 : $i]:
% 0.37/0.57         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.57  thf(t79_tops_1, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.57                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( l1_pre_topc @ A ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57              ( ![C:$i]:
% 0.37/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                  ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.57                    ( v1_tops_1 @ C @ A ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t79_tops_1])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_k2_pre_topc, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @
% 0.37/0.57         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['0', '5'])).
% 0.37/0.57  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_l1_pre_topc, axiom,
% 0.37/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.57  thf('8', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.57  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '9'])).
% 0.37/0.57  thf(t2_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i]:
% 0.37/0.57         ((r2_hidden @ X10 @ X11)
% 0.37/0.57          | (v1_xboole_0 @ X11)
% 0.37/0.57          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | (r2_hidden @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf(d10_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.57  thf(d1_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.37/0.57          | (r2_hidden @ X3 @ X5)
% 0.37/0.57          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.57  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '16'])).
% 0.37/0.57  thf(dt_k2_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.57  thf('19', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('20', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.37/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.57  thf(t5_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X12 @ X13)
% 0.37/0.57          | ~ (v1_xboole_0 @ X14)
% 0.37/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      ((r2_hidden @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['12', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ X5)
% 0.37/0.57          | (r1_tarski @ X6 @ X4)
% 0.37/0.57          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ (k2_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['24', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C_1))
% 0.37/0.57        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d3_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.37/0.57             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ((k2_pre_topc @ X23 @ X22) != (k2_struct_0 @ X23))
% 0.37/0.57          | (v1_tops_1 @ X22 @ X23)
% 0.37/0.57          | ~ (l1_pre_topc @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v1_tops_1 @ sk_C_1 @ sk_A)
% 0.37/0.57        | ((k2_pre_topc @ sk_A @ sk_C_1) != (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (((v1_tops_1 @ sk_C_1 @ sk_A)
% 0.37/0.57        | ((k2_pre_topc @ sk_A @ sk_C_1) != (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain, (~ (v1_tops_1 @ sk_C_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('36', plain, (((k2_pre_topc @ sk_A @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['34', '35'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C_1))),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['29', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X15 : $i]:
% 0.37/0.57         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.57  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t49_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57               ( ( r1_tarski @ B @ C ) =>
% 0.37/0.57                 ( r1_tarski @
% 0.37/0.57                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.57          | ~ (r1_tarski @ X19 @ X21)
% 0.37/0.57          | (r1_tarski @ (k2_pre_topc @ X20 @ X19) @ (k2_pre_topc @ X20 @ X21))
% 0.37/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.57          | ~ (l1_pre_topc @ X20))),
% 0.37/0.57      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (![X15 : $i]:
% 0.37/0.57         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i]:
% 0.37/0.57         ((r2_hidden @ X10 @ X11)
% 0.37/0.57          | (v1_xboole_0 @ X11)
% 0.37/0.57          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | (r2_hidden @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.57  thf('56', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      ((r2_hidden @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ~ (v1_tops_1 @ X22 @ X23)
% 0.37/0.57          | ((k2_pre_topc @ X23 @ X22) = (k2_struct_0 @ X23))
% 0.37/0.57          | ~ (l1_pre_topc @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.37/0.57        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('64', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('65', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.37/0.57  thf('66', plain, ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['59', '65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.37/0.57        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.37/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['48', '68'])).
% 0.37/0.57  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.57  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('72', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.37/0.57  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.57          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.37/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['47', '72', '73'])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.37/0.57        | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '74'])).
% 0.37/0.57  thf('76', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      ((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C_1))),
% 0.37/0.57      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.57  thf('78', plain, ($false), inference('demod', [status(thm)], ['37', '77'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
