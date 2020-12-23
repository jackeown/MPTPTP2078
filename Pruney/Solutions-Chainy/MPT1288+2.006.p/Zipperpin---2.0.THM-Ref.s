%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8eaE7rXLx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:58 EST 2020

% Result     : Theorem 7.60s
% Output     : Refutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 302 expanded)
%              Number of leaves         :   36 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          : 1320 (3799 expanded)
%              Number of equality atoms :   36 ( 144 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ ( k2_tops_1 @ X27 @ ( k2_tops_1 @ X27 @ X26 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t94_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_tops_1 @ X34 @ X35 )
      | ( X34
        = ( k2_tops_1 @ X35 @ X34 ) )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t96_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X37 @ X36 ) @ X37 )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t96_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('32',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k2_pre_topc @ X8 @ ( k2_pre_topc @ X8 @ X9 ) )
        = ( k2_pre_topc @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf('41',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29','40'])).

thf('42',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','24','41'])).

thf('43',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( ( k7_subset_1 @ X4 @ X3 @ X5 )
        = ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ X10 @ ( k2_pre_topc @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ~ ( r1_tarski @ X31 @ X33 )
      | ( r1_tarski @ X31 @ ( k1_tops_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('84',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','91'])).

thf('93',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('99',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','99'])).

thf('101',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','100'])).

thf('102',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8eaE7rXLx
% 0.15/0.37  % Computer   : n019.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:53:22 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 7.60/7.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.60/7.79  % Solved by: fo/fo7.sh
% 7.60/7.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.60/7.79  % done 7724 iterations in 7.304s
% 7.60/7.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.60/7.79  % SZS output start Refutation
% 7.60/7.79  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 7.60/7.79  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 7.60/7.79  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.60/7.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.60/7.79  thf(sk_A_type, type, sk_A: $i).
% 7.60/7.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.60/7.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.60/7.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.60/7.79  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 7.60/7.79  thf(sk_B_type, type, sk_B: $i).
% 7.60/7.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.60/7.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.60/7.79  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.60/7.79  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.60/7.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.60/7.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.60/7.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.60/7.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.60/7.79  thf(t110_tops_1, conjecture,
% 7.60/7.79    (![A:$i]:
% 7.60/7.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.60/7.79       ( ![B:$i]:
% 7.60/7.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.79           ( ( v4_tops_1 @ B @ A ) =>
% 7.60/7.79             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 7.60/7.79  thf(zf_stmt_0, negated_conjecture,
% 7.60/7.79    (~( ![A:$i]:
% 7.60/7.79        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.60/7.79          ( ![B:$i]:
% 7.60/7.79            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.79              ( ( v4_tops_1 @ B @ A ) =>
% 7.60/7.79                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 7.60/7.79    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 7.60/7.79  thf('0', plain,
% 7.60/7.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf(dt_k2_pre_topc, axiom,
% 7.60/7.79    (![A:$i,B:$i]:
% 7.60/7.79     ( ( ( l1_pre_topc @ A ) & 
% 7.60/7.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.79       ( m1_subset_1 @
% 7.60/7.79         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.60/7.79  thf('1', plain,
% 7.60/7.79      (![X6 : $i, X7 : $i]:
% 7.60/7.79         (~ (l1_pre_topc @ X6)
% 7.60/7.79          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 7.60/7.79          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 7.60/7.79             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 7.60/7.79      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.60/7.79  thf('2', plain,
% 7.60/7.79      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['0', '1'])).
% 7.60/7.79  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('4', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.79  thf(l80_tops_1, axiom,
% 7.60/7.79    (![A:$i]:
% 7.60/7.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.60/7.79       ( ![B:$i]:
% 7.60/7.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.79           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 7.60/7.79             ( k1_xboole_0 ) ) ) ) ))).
% 7.60/7.79  thf('5', plain,
% 7.60/7.79      (![X26 : $i, X27 : $i]:
% 7.60/7.79         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 7.60/7.79          | ((k1_tops_1 @ X27 @ (k2_tops_1 @ X27 @ (k2_tops_1 @ X27 @ X26)))
% 7.60/7.79              = (k1_xboole_0))
% 7.60/7.79          | ~ (l1_pre_topc @ X27)
% 7.60/7.79          | ~ (v2_pre_topc @ X27))),
% 7.60/7.79      inference('cnf', [status(esa)], [l80_tops_1])).
% 7.60/7.79  thf('6', plain,
% 7.60/7.79      ((~ (v2_pre_topc @ sk_A)
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A)
% 7.60/7.79        | ((k1_tops_1 @ sk_A @ 
% 7.60/7.79            (k2_tops_1 @ sk_A @ 
% 7.60/7.79             (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 7.60/7.79            = (k1_xboole_0)))),
% 7.60/7.79      inference('sup-', [status(thm)], ['4', '5'])).
% 7.60/7.79  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('9', plain,
% 7.60/7.79      (((k1_tops_1 @ sk_A @ 
% 7.60/7.79         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 7.60/7.79         = (k1_xboole_0))),
% 7.60/7.79      inference('demod', [status(thm)], ['6', '7', '8'])).
% 7.60/7.79  thf('10', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.79  thf(dt_k2_tops_1, axiom,
% 7.60/7.79    (![A:$i,B:$i]:
% 7.60/7.79     ( ( ( l1_pre_topc @ A ) & 
% 7.60/7.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.79       ( m1_subset_1 @
% 7.60/7.79         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.60/7.79  thf('11', plain,
% 7.60/7.79      (![X16 : $i, X17 : $i]:
% 7.60/7.79         (~ (l1_pre_topc @ X16)
% 7.60/7.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 7.60/7.79          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 7.60/7.79             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 7.60/7.79      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.60/7.79  thf('12', plain,
% 7.60/7.79      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['10', '11'])).
% 7.60/7.79  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('14', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['12', '13'])).
% 7.60/7.79  thf(t94_tops_1, axiom,
% 7.60/7.79    (![A:$i]:
% 7.60/7.79     ( ( l1_pre_topc @ A ) =>
% 7.60/7.79       ( ![B:$i]:
% 7.60/7.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.79           ( ( v4_pre_topc @ B @ A ) =>
% 7.60/7.79             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 7.60/7.79  thf('15', plain,
% 7.60/7.79      (![X34 : $i, X35 : $i]:
% 7.60/7.79         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 7.60/7.79          | ~ (v3_tops_1 @ X34 @ X35)
% 7.60/7.79          | ((X34) = (k2_tops_1 @ X35 @ X34))
% 7.60/7.79          | ~ (v4_pre_topc @ X34 @ X35)
% 7.60/7.79          | ~ (l1_pre_topc @ X35))),
% 7.60/7.79      inference('cnf', [status(esa)], [t94_tops_1])).
% 7.60/7.79  thf('16', plain,
% 7.60/7.79      ((~ (l1_pre_topc @ sk_A)
% 7.60/7.79        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79             sk_A)
% 7.60/7.79        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.79            = (k2_tops_1 @ sk_A @ 
% 7.60/7.79               (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 7.60/7.79        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79             sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['14', '15'])).
% 7.60/7.79  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('18', plain,
% 7.60/7.79      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79           sk_A)
% 7.60/7.79        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.79            = (k2_tops_1 @ sk_A @ 
% 7.60/7.79               (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 7.60/7.79        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79             sk_A))),
% 7.60/7.79      inference('demod', [status(thm)], ['16', '17'])).
% 7.60/7.79  thf('19', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.79  thf(fc11_tops_1, axiom,
% 7.60/7.79    (![A:$i,B:$i]:
% 7.60/7.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.60/7.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.79       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 7.60/7.79  thf('20', plain,
% 7.60/7.79      (![X18 : $i, X19 : $i]:
% 7.60/7.79         (~ (l1_pre_topc @ X18)
% 7.60/7.79          | ~ (v2_pre_topc @ X18)
% 7.60/7.79          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 7.60/7.79          | (v4_pre_topc @ (k2_tops_1 @ X18 @ X19) @ X18))),
% 7.60/7.79      inference('cnf', [status(esa)], [fc11_tops_1])).
% 7.60/7.79  thf('21', plain,
% 7.60/7.79      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 7.60/7.79        | ~ (v2_pre_topc @ sk_A)
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['19', '20'])).
% 7.60/7.79  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('24', plain,
% 7.60/7.79      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 7.60/7.79      inference('demod', [status(thm)], ['21', '22', '23'])).
% 7.60/7.79  thf('25', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.79  thf(t96_tops_1, axiom,
% 7.60/7.79    (![A:$i]:
% 7.60/7.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.60/7.79       ( ![B:$i]:
% 7.60/7.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.79           ( ( v4_pre_topc @ B @ A ) =>
% 7.60/7.79             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 7.60/7.79  thf('26', plain,
% 7.60/7.79      (![X36 : $i, X37 : $i]:
% 7.60/7.79         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 7.60/7.79          | (v3_tops_1 @ (k2_tops_1 @ X37 @ X36) @ X37)
% 7.60/7.79          | ~ (v4_pre_topc @ X36 @ X37)
% 7.60/7.79          | ~ (l1_pre_topc @ X37)
% 7.60/7.79          | ~ (v2_pre_topc @ X37))),
% 7.60/7.79      inference('cnf', [status(esa)], [t96_tops_1])).
% 7.60/7.79  thf('27', plain,
% 7.60/7.79      ((~ (v2_pre_topc @ sk_A)
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A)
% 7.60/7.79        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 7.60/7.79        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['25', '26'])).
% 7.60/7.79  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf('30', plain,
% 7.60/7.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.79  thf(fc1_tops_1, axiom,
% 7.60/7.79    (![A:$i,B:$i]:
% 7.60/7.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.60/7.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.79       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 7.60/7.79  thf('31', plain,
% 7.60/7.79      (![X20 : $i, X21 : $i]:
% 7.60/7.79         (~ (l1_pre_topc @ X20)
% 7.60/7.79          | ~ (v2_pre_topc @ X20)
% 7.60/7.79          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 7.60/7.79          | (v4_pre_topc @ (k2_pre_topc @ X20 @ X21) @ X20))),
% 7.60/7.79      inference('cnf', [status(esa)], [fc1_tops_1])).
% 7.60/7.79  thf('32', plain,
% 7.60/7.79      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.79         sk_A)
% 7.60/7.79        | ~ (v2_pre_topc @ sk_A)
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.79      inference('sup-', [status(thm)], ['30', '31'])).
% 7.60/7.79  thf('33', plain,
% 7.60/7.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.79  thf(projectivity_k2_pre_topc, axiom,
% 7.60/7.79    (![A:$i,B:$i]:
% 7.60/7.79     ( ( ( l1_pre_topc @ A ) & 
% 7.60/7.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.79       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 7.60/7.79         ( k2_pre_topc @ A @ B ) ) ))).
% 7.60/7.79  thf('34', plain,
% 7.60/7.79      (![X8 : $i, X9 : $i]:
% 7.60/7.79         (~ (l1_pre_topc @ X8)
% 7.60/7.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 7.60/7.79          | ((k2_pre_topc @ X8 @ (k2_pre_topc @ X8 @ X9))
% 7.60/7.79              = (k2_pre_topc @ X8 @ X9)))),
% 7.60/7.79      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 7.60/7.79  thf('35', plain,
% 7.60/7.79      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.79          = (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.79        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.80      inference('sup-', [status(thm)], ['33', '34'])).
% 7.60/7.80  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('37', plain,
% 7.60/7.80      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.60/7.80      inference('demod', [status(thm)], ['35', '36'])).
% 7.60/7.80  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('40', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 7.60/7.80      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 7.60/7.80  thf('41', plain,
% 7.60/7.80      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 7.60/7.80      inference('demod', [status(thm)], ['27', '28', '29', '40'])).
% 7.60/7.80  thf('42', plain,
% 7.60/7.80      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.60/7.80      inference('demod', [status(thm)], ['18', '24', '41'])).
% 7.60/7.80  thf('43', plain,
% 7.60/7.80      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.60/7.80         = (k1_xboole_0))),
% 7.60/7.80      inference('demod', [status(thm)], ['9', '42'])).
% 7.60/7.80  thf('44', plain,
% 7.60/7.80      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.80  thf(l78_tops_1, axiom,
% 7.60/7.80    (![A:$i]:
% 7.60/7.80     ( ( l1_pre_topc @ A ) =>
% 7.60/7.80       ( ![B:$i]:
% 7.60/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80           ( ( k2_tops_1 @ A @ B ) =
% 7.60/7.80             ( k7_subset_1 @
% 7.60/7.80               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 7.60/7.80               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.60/7.80  thf('45', plain,
% 7.60/7.80      (![X24 : $i, X25 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.60/7.80          | ((k2_tops_1 @ X25 @ X24)
% 7.60/7.80              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 7.60/7.80                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 7.60/7.80          | ~ (l1_pre_topc @ X25))),
% 7.60/7.80      inference('cnf', [status(esa)], [l78_tops_1])).
% 7.60/7.80  thf('46', plain,
% 7.60/7.80      ((~ (l1_pre_topc @ sk_A)
% 7.60/7.80        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.60/7.80               (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 7.60/7.80      inference('sup-', [status(thm)], ['44', '45'])).
% 7.60/7.80  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('48', plain,
% 7.60/7.80      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.60/7.80      inference('demod', [status(thm)], ['35', '36'])).
% 7.60/7.80  thf('49', plain,
% 7.60/7.80      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.80  thf(redefinition_k7_subset_1, axiom,
% 7.60/7.80    (![A:$i,B:$i,C:$i]:
% 7.60/7.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.60/7.80       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 7.60/7.80  thf('50', plain,
% 7.60/7.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 7.60/7.80          | ((k7_subset_1 @ X4 @ X3 @ X5) = (k4_xboole_0 @ X3 @ X5)))),
% 7.60/7.80      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.60/7.80  thf('51', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 7.60/7.80      inference('sup-', [status(thm)], ['49', '50'])).
% 7.60/7.80  thf('52', plain,
% 7.60/7.80      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.60/7.80      inference('demod', [status(thm)], ['46', '47', '48', '51'])).
% 7.60/7.80  thf('53', plain,
% 7.60/7.80      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.80  thf('54', plain,
% 7.60/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf(t48_tops_1, axiom,
% 7.60/7.80    (![A:$i]:
% 7.60/7.80     ( ( l1_pre_topc @ A ) =>
% 7.60/7.80       ( ![B:$i]:
% 7.60/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80           ( ![C:$i]:
% 7.60/7.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80               ( ( r1_tarski @ B @ C ) =>
% 7.60/7.80                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.60/7.80  thf('55', plain,
% 7.60/7.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 7.60/7.80          | ~ (r1_tarski @ X28 @ X30)
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 7.60/7.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 7.60/7.80          | ~ (l1_pre_topc @ X29))),
% 7.60/7.80      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.60/7.80  thf('56', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         (~ (l1_pre_topc @ sk_A)
% 7.60/7.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 7.60/7.80          | ~ (r1_tarski @ sk_B @ X0))),
% 7.60/7.80      inference('sup-', [status(thm)], ['54', '55'])).
% 7.60/7.80  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('58', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 7.60/7.80          | ~ (r1_tarski @ sk_B @ X0))),
% 7.60/7.80      inference('demod', [status(thm)], ['56', '57'])).
% 7.60/7.80  thf('59', plain,
% 7.60/7.80      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.60/7.80           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.60/7.80      inference('sup-', [status(thm)], ['53', '58'])).
% 7.60/7.80  thf('60', plain,
% 7.60/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf(t48_pre_topc, axiom,
% 7.60/7.80    (![A:$i]:
% 7.60/7.80     ( ( l1_pre_topc @ A ) =>
% 7.60/7.80       ( ![B:$i]:
% 7.60/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 7.60/7.80  thf('61', plain,
% 7.60/7.80      (![X10 : $i, X11 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 7.60/7.80          | (r1_tarski @ X10 @ (k2_pre_topc @ X11 @ X10))
% 7.60/7.80          | ~ (l1_pre_topc @ X11))),
% 7.60/7.80      inference('cnf', [status(esa)], [t48_pre_topc])).
% 7.60/7.80  thf('62', plain,
% 7.60/7.80      ((~ (l1_pre_topc @ sk_A)
% 7.60/7.80        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.60/7.80      inference('sup-', [status(thm)], ['60', '61'])).
% 7.60/7.80  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('64', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 7.60/7.80      inference('demod', [status(thm)], ['62', '63'])).
% 7.60/7.80  thf('65', plain,
% 7.60/7.80      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.60/7.80      inference('demod', [status(thm)], ['59', '64'])).
% 7.60/7.80  thf(d10_xboole_0, axiom,
% 7.60/7.80    (![A:$i,B:$i]:
% 7.60/7.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.60/7.80  thf('66', plain,
% 7.60/7.80      (![X0 : $i, X2 : $i]:
% 7.60/7.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.60/7.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.60/7.80  thf('67', plain,
% 7.60/7.80      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80           (k1_tops_1 @ sk_A @ sk_B))
% 7.60/7.80        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80            = (k1_tops_1 @ sk_A @ sk_B)))),
% 7.60/7.80      inference('sup-', [status(thm)], ['65', '66'])).
% 7.60/7.80  thf('68', plain,
% 7.60/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf(d6_tops_1, axiom,
% 7.60/7.80    (![A:$i]:
% 7.60/7.80     ( ( l1_pre_topc @ A ) =>
% 7.60/7.80       ( ![B:$i]:
% 7.60/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80           ( ( v4_tops_1 @ B @ A ) <=>
% 7.60/7.80             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 7.60/7.80               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 7.60/7.80  thf('69', plain,
% 7.60/7.80      (![X12 : $i, X13 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 7.60/7.80          | ~ (v4_tops_1 @ X12 @ X13)
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 7.60/7.80          | ~ (l1_pre_topc @ X13))),
% 7.60/7.80      inference('cnf', [status(esa)], [d6_tops_1])).
% 7.60/7.80  thf('70', plain,
% 7.60/7.80      ((~ (l1_pre_topc @ sk_A)
% 7.60/7.80        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 7.60/7.80        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 7.60/7.80      inference('sup-', [status(thm)], ['68', '69'])).
% 7.60/7.80  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('72', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('73', plain,
% 7.60/7.80      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 7.60/7.80      inference('demod', [status(thm)], ['70', '71', '72'])).
% 7.60/7.80  thf('74', plain,
% 7.60/7.80      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.80  thf(dt_k1_tops_1, axiom,
% 7.60/7.80    (![A:$i,B:$i]:
% 7.60/7.80     ( ( ( l1_pre_topc @ A ) & 
% 7.60/7.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.80       ( m1_subset_1 @
% 7.60/7.80         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.60/7.80  thf('75', plain,
% 7.60/7.80      (![X14 : $i, X15 : $i]:
% 7.60/7.80         (~ (l1_pre_topc @ X14)
% 7.60/7.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 7.60/7.80          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 7.60/7.80             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 7.60/7.80      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.60/7.80  thf('76', plain,
% 7.60/7.80      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.80        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.80      inference('sup-', [status(thm)], ['74', '75'])).
% 7.60/7.80  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('78', plain,
% 7.60/7.80      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['76', '77'])).
% 7.60/7.80  thf(t56_tops_1, axiom,
% 7.60/7.80    (![A:$i]:
% 7.60/7.80     ( ( l1_pre_topc @ A ) =>
% 7.60/7.80       ( ![B:$i]:
% 7.60/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80           ( ![C:$i]:
% 7.60/7.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.60/7.80               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 7.60/7.80                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.60/7.80  thf('79', plain,
% 7.60/7.80      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.60/7.80          | ~ (v3_pre_topc @ X31 @ X32)
% 7.60/7.80          | ~ (r1_tarski @ X31 @ X33)
% 7.60/7.80          | (r1_tarski @ X31 @ (k1_tops_1 @ X32 @ X33))
% 7.60/7.80          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.60/7.80          | ~ (l1_pre_topc @ X32))),
% 7.60/7.80      inference('cnf', [status(esa)], [t56_tops_1])).
% 7.60/7.80  thf('80', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         (~ (l1_pre_topc @ sk_A)
% 7.60/7.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80             (k1_tops_1 @ sk_A @ X0))
% 7.60/7.80          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80               X0)
% 7.60/7.80          | ~ (v3_pre_topc @ 
% 7.60/7.80               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 7.60/7.80      inference('sup-', [status(thm)], ['78', '79'])).
% 7.60/7.80  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('82', plain,
% 7.60/7.80      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('demod', [status(thm)], ['2', '3'])).
% 7.60/7.80  thf(fc9_tops_1, axiom,
% 7.60/7.80    (![A:$i,B:$i]:
% 7.60/7.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.60/7.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.60/7.80       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 7.60/7.80  thf('83', plain,
% 7.60/7.80      (![X22 : $i, X23 : $i]:
% 7.60/7.80         (~ (l1_pre_topc @ X22)
% 7.60/7.80          | ~ (v2_pre_topc @ X22)
% 7.60/7.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 7.60/7.80          | (v3_pre_topc @ (k1_tops_1 @ X22 @ X23) @ X22))),
% 7.60/7.80      inference('cnf', [status(esa)], [fc9_tops_1])).
% 7.60/7.80  thf('84', plain,
% 7.60/7.80      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 7.60/7.80        | ~ (v2_pre_topc @ sk_A)
% 7.60/7.80        | ~ (l1_pre_topc @ sk_A))),
% 7.60/7.80      inference('sup-', [status(thm)], ['82', '83'])).
% 7.60/7.80  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('87', plain,
% 7.60/7.80      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 7.60/7.80      inference('demod', [status(thm)], ['84', '85', '86'])).
% 7.60/7.80  thf('88', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.60/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80             (k1_tops_1 @ sk_A @ X0))
% 7.60/7.80          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80               X0))),
% 7.60/7.80      inference('demod', [status(thm)], ['80', '81', '87'])).
% 7.60/7.80  thf('89', plain,
% 7.60/7.80      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80         (k1_tops_1 @ sk_A @ sk_B))
% 7.60/7.80        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.60/7.80      inference('sup-', [status(thm)], ['73', '88'])).
% 7.60/7.80  thf('90', plain,
% 7.60/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('91', plain,
% 7.60/7.80      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.60/7.80        (k1_tops_1 @ sk_A @ sk_B))),
% 7.60/7.80      inference('demod', [status(thm)], ['89', '90'])).
% 7.60/7.80  thf('92', plain,
% 7.60/7.80      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.60/7.80      inference('demod', [status(thm)], ['67', '91'])).
% 7.60/7.80  thf('93', plain,
% 7.60/7.80      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.60/7.80         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80            (k1_tops_1 @ sk_A @ sk_B)))),
% 7.60/7.80      inference('demod', [status(thm)], ['52', '92'])).
% 7.60/7.80  thf('94', plain,
% 7.60/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('95', plain,
% 7.60/7.80      (![X24 : $i, X25 : $i]:
% 7.60/7.80         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.60/7.80          | ((k2_tops_1 @ X25 @ X24)
% 7.60/7.80              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 7.60/7.80                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 7.60/7.80          | ~ (l1_pre_topc @ X25))),
% 7.60/7.80      inference('cnf', [status(esa)], [l78_tops_1])).
% 7.60/7.80  thf('96', plain,
% 7.60/7.80      ((~ (l1_pre_topc @ sk_A)
% 7.60/7.80        | ((k2_tops_1 @ sk_A @ sk_B)
% 7.60/7.80            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.60/7.80               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.60/7.80      inference('sup-', [status(thm)], ['94', '95'])).
% 7.60/7.80  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('98', plain,
% 7.60/7.80      (![X0 : $i]:
% 7.60/7.80         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 7.60/7.80      inference('sup-', [status(thm)], ['49', '50'])).
% 7.60/7.80  thf('99', plain,
% 7.60/7.80      (((k2_tops_1 @ sk_A @ sk_B)
% 7.60/7.80         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.60/7.80            (k1_tops_1 @ sk_A @ sk_B)))),
% 7.60/7.80      inference('demod', [status(thm)], ['96', '97', '98'])).
% 7.60/7.80  thf('100', plain,
% 7.60/7.80      (((k2_tops_1 @ sk_A @ sk_B)
% 7.60/7.80         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.60/7.80      inference('sup+', [status(thm)], ['93', '99'])).
% 7.60/7.80  thf('101', plain,
% 7.60/7.80      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 7.60/7.80      inference('demod', [status(thm)], ['43', '100'])).
% 7.60/7.80  thf('102', plain,
% 7.60/7.80      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 7.60/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.60/7.80  thf('103', plain, ($false),
% 7.60/7.80      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 7.60/7.80  
% 7.60/7.80  % SZS output end Refutation
% 7.60/7.80  
% 7.65/7.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
