%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kpV51l0DVb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 176 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  983 (2275 expanded)
%              Number of equality atoms :   64 ( 120 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('10',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','24','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ ( k2_tops_1 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_pre_topc @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
       != X19 )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kpV51l0DVb
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 190 iterations in 0.123s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.61  thf(t77_tops_1, conjecture,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.61             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.61               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i]:
% 0.36/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.61          ( ![B:$i]:
% 0.36/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.61                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.61                  ( k7_subset_1 @
% 0.36/0.61                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      (~
% 0.36/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t74_tops_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_pre_topc @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61           ( ( k1_tops_1 @ A @ B ) =
% 0.36/0.61             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X27 : $i, X28 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.61          | ((k1_tops_1 @ X28 @ X27)
% 0.36/0.61              = (k7_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.36/0.61                 (k2_tops_1 @ X28 @ X27)))
% 0.36/0.61          | ~ (l1_pre_topc @ X28))),
% 0.36/0.61      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.61        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.61            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.36/0.61          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      (((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.61         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.61      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('split', [status(esa)], ['10'])).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t69_tops_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_pre_topc @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61           ( ( v4_pre_topc @ B @ A ) =>
% 0.36/0.61             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      (![X25 : $i, X26 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.61          | (r1_tarski @ (k2_tops_1 @ X26 @ X25) @ X25)
% 0.36/0.61          | ~ (v4_pre_topc @ X25 @ X26)
% 0.36/0.61          | ~ (l1_pre_topc @ X26))),
% 0.36/0.61      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['11', '16'])).
% 0.36/0.61  thf(t3_subset, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      (![X16 : $i, X18 : $i]:
% 0.36/0.61         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      (![X8 : $i, X9 : $i]:
% 0.36/0.61         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 0.36/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.36/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.61  thf(d5_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (![X6 : $i, X7 : $i]:
% 0.36/0.61         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.36/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.61          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.61  thf(t36_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.36/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X16 : $i, X18 : $i]:
% 0.36/0.61         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      (![X6 : $i, X7 : $i]:
% 0.36/0.61         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.36/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.61           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['21', '24', '29'])).
% 0.36/0.61  thf('31', plain,
% 0.36/0.61      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['9', '30'])).
% 0.36/0.61  thf('32', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.36/0.61             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['31', '34'])).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.61       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('split', [status(esa)], ['10'])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(dt_k2_tops_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.61       ( m1_subset_1 @
% 0.36/0.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      (![X21 : $i, X22 : $i]:
% 0.36/0.61         (~ (l1_pre_topc @ X21)
% 0.36/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.61          | (m1_subset_1 @ (k2_tops_1 @ X21 @ X22) @ 
% 0.36/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.36/0.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.36/0.61  thf('40', plain,
% 0.36/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.61  thf('44', plain,
% 0.36/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.36/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 0.36/0.61          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.61            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.61  thf('46', plain,
% 0.36/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['42', '45'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t65_tops_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_pre_topc @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.61  thf('48', plain,
% 0.36/0.61      (![X23 : $i, X24 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.61          | ((k2_pre_topc @ X24 @ X23)
% 0.36/0.61              = (k4_subset_1 @ (u1_struct_0 @ X24) @ X23 @ 
% 0.36/0.61                 (k2_tops_1 @ X24 @ X23)))
% 0.36/0.61          | ~ (l1_pre_topc @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.61  thf('49', plain,
% 0.36/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.61        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.61  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('51', plain,
% 0.36/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.61         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['46', '51'])).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('split', [status(esa)], ['10'])).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('sup+', [status(thm)], ['53', '54'])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.36/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.61  thf(t12_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.61  thf('57', plain,
% 0.36/0.61      (![X2 : $i, X3 : $i]:
% 0.36/0.61         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.61  thf('58', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.61  thf('59', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.36/0.61      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.61  thf('61', plain,
% 0.36/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('sup+', [status(thm)], ['55', '60'])).
% 0.36/0.61  thf('62', plain,
% 0.36/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('sup+', [status(thm)], ['52', '61'])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t52_pre_topc, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_pre_topc @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      (![X19 : $i, X20 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.61          | ~ (v2_pre_topc @ X20)
% 0.36/0.61          | ((k2_pre_topc @ X20 @ X19) != (X19))
% 0.36/0.61          | (v4_pre_topc @ X19 @ X20)
% 0.36/0.61          | ~ (l1_pre_topc @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.61  thf('65', plain,
% 0.36/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.61        | (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.61        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.36/0.61        | ~ (v2_pre_topc @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.61  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('68', plain,
% 0.36/0.61      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.36/0.61      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.36/0.61  thf('69', plain,
% 0.36/0.61      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['62', '68'])).
% 0.36/0.61  thf('70', plain,
% 0.36/0.61      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.61      inference('simplify', [status(thm)], ['69'])).
% 0.36/0.61  thf('71', plain,
% 0.36/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('72', plain,
% 0.36/0.61      (~
% 0.36/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.61       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.61  thf('73', plain, ($false),
% 0.36/0.61      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '72'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
