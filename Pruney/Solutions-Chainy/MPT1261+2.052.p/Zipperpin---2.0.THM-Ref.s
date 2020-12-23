%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwYNLVEZzT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:45 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 726 expanded)
%              Number of leaves         :   43 ( 247 expanded)
%              Depth                    :   17
%              Number of atoms          : 1637 (7182 expanded)
%              Number of equality atoms :  116 ( 516 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X54 @ X53 ) @ X53 )
      | ~ ( v4_pre_topc @ X53 @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','37','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('43',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','51','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k3_subset_1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','51','52'])).

thf('61',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','37','40'])).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','37','40'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','37','40'])).

thf('75',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('76',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','36','37','40'])).

thf('78',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','76','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('87',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('94',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('103',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('104',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('105',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k3_tarski @ ( k2_tarski @ X34 @ X36 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('122',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('123',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('124',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['107','125'])).

thf('127',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('129',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 @ ( k2_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['127','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('135',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X47 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('136',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['133','139'])).

thf('141',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','84','85','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwYNLVEZzT
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:19:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.50/2.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.50/2.75  % Solved by: fo/fo7.sh
% 2.50/2.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.50/2.75  % done 3316 iterations in 2.268s
% 2.50/2.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.50/2.75  % SZS output start Refutation
% 2.50/2.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.50/2.75  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.50/2.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.50/2.75  thf(sk_A_type, type, sk_A: $i).
% 2.50/2.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.50/2.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.50/2.75  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.50/2.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.50/2.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.50/2.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.50/2.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.50/2.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.50/2.75  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.50/2.75  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.50/2.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.50/2.75  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.50/2.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.50/2.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.50/2.75  thf(sk_B_type, type, sk_B: $i).
% 2.50/2.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.50/2.75  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.50/2.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.50/2.75  thf(t77_tops_1, conjecture,
% 2.50/2.75    (![A:$i]:
% 2.50/2.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.50/2.75       ( ![B:$i]:
% 2.50/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.50/2.75           ( ( v4_pre_topc @ B @ A ) <=>
% 2.50/2.75             ( ( k2_tops_1 @ A @ B ) =
% 2.50/2.75               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.50/2.75  thf(zf_stmt_0, negated_conjecture,
% 2.50/2.75    (~( ![A:$i]:
% 2.50/2.75        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.50/2.75          ( ![B:$i]:
% 2.50/2.75            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.50/2.75              ( ( v4_pre_topc @ B @ A ) <=>
% 2.50/2.75                ( ( k2_tops_1 @ A @ B ) =
% 2.50/2.75                  ( k7_subset_1 @
% 2.50/2.75                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.50/2.75    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 2.50/2.75  thf('0', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75              (k1_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('1', plain,
% 2.50/2.75      (~
% 2.50/2.75       (((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.50/2.75       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('split', [status(esa)], ['0'])).
% 2.50/2.75  thf('2', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75        | (v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('3', plain,
% 2.50/2.75      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('split', [status(esa)], ['2'])).
% 2.50/2.75  thf('4', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(t69_tops_1, axiom,
% 2.50/2.75    (![A:$i]:
% 2.50/2.75     ( ( l1_pre_topc @ A ) =>
% 2.50/2.75       ( ![B:$i]:
% 2.50/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.50/2.75           ( ( v4_pre_topc @ B @ A ) =>
% 2.50/2.75             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 2.50/2.75  thf('5', plain,
% 2.50/2.75      (![X53 : $i, X54 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 2.50/2.75          | (r1_tarski @ (k2_tops_1 @ X54 @ X53) @ X53)
% 2.50/2.75          | ~ (v4_pre_topc @ X53 @ X54)
% 2.50/2.75          | ~ (l1_pre_topc @ X54))),
% 2.50/2.75      inference('cnf', [status(esa)], [t69_tops_1])).
% 2.50/2.75  thf('6', plain,
% 2.50/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.50/2.75        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 2.50/2.75        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.50/2.75      inference('sup-', [status(thm)], ['4', '5'])).
% 2.50/2.75  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('8', plain,
% 2.50/2.75      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 2.50/2.75        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.50/2.75      inference('demod', [status(thm)], ['6', '7'])).
% 2.50/2.75  thf('9', plain,
% 2.50/2.75      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['3', '8'])).
% 2.50/2.75  thf(t1_boole, axiom,
% 2.50/2.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.50/2.75  thf('10', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 2.50/2.75      inference('cnf', [status(esa)], [t1_boole])).
% 2.50/2.75  thf(l51_zfmisc_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.50/2.75  thf('11', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('12', plain,
% 2.50/2.75      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 2.50/2.75      inference('demod', [status(thm)], ['10', '11'])).
% 2.50/2.75  thf(t43_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i,C:$i]:
% 2.50/2.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.50/2.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.50/2.75  thf('13', plain,
% 2.50/2.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.50/2.75         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 2.50/2.75          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 2.50/2.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.50/2.75  thf('14', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('15', plain,
% 2.50/2.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.50/2.75         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 2.50/2.75          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 2.50/2.75      inference('demod', [status(thm)], ['13', '14'])).
% 2.50/2.75  thf('16', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         (~ (r1_tarski @ X1 @ X0)
% 2.50/2.75          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['12', '15'])).
% 2.50/2.75  thf('17', plain,
% 2.50/2.75      (((r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 2.50/2.75         k1_xboole_0)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['9', '16'])).
% 2.50/2.75  thf(t7_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.50/2.75  thf('18', plain,
% 2.50/2.75      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.50/2.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.50/2.75  thf('19', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('20', plain,
% 2.50/2.75      (![X22 : $i, X23 : $i]:
% 2.50/2.75         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 2.50/2.75      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.75  thf('21', plain,
% 2.50/2.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.50/2.75         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 2.50/2.75          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 2.50/2.75      inference('demod', [status(thm)], ['13', '14'])).
% 2.50/2.75  thf('22', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 2.50/2.75      inference('sup-', [status(thm)], ['20', '21'])).
% 2.50/2.75  thf(t38_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 2.50/2.75       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.50/2.75  thf('23', plain,
% 2.50/2.75      (![X11 : $i, X12 : $i]:
% 2.50/2.75         (((X11) = (k1_xboole_0))
% 2.50/2.75          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 2.50/2.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 2.50/2.75  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['22', '23'])).
% 2.50/2.75  thf('25', plain,
% 2.50/2.75      (![X11 : $i, X12 : $i]:
% 2.50/2.75         (((X11) = (k1_xboole_0))
% 2.50/2.75          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 2.50/2.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 2.50/2.75  thf('26', plain,
% 2.50/2.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['24', '25'])).
% 2.50/2.75  thf('27', plain,
% 2.50/2.75      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['17', '26'])).
% 2.50/2.75  thf(t51_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.50/2.75       ( A ) ))).
% 2.50/2.75  thf('28', plain,
% 2.50/2.75      (![X20 : $i, X21 : $i]:
% 2.50/2.75         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 2.50/2.75           = (X20))),
% 2.50/2.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.50/2.75  thf('29', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('30', plain,
% 2.50/2.75      (![X20 : $i, X21 : $i]:
% 2.50/2.75         ((k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21)))
% 2.50/2.75           = (X20))),
% 2.50/2.75      inference('demod', [status(thm)], ['28', '29'])).
% 2.50/2.75  thf('31', plain,
% 2.50/2.75      ((((k3_tarski @ 
% 2.50/2.75          (k2_tarski @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 2.50/2.75           k1_xboole_0))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup+', [status(thm)], ['27', '30'])).
% 2.50/2.75  thf(commutativity_k2_tarski, axiom,
% 2.50/2.75    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.50/2.75  thf('32', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf(t12_setfam_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.50/2.75  thf('33', plain,
% 2.50/2.75      (![X40 : $i, X41 : $i]:
% 2.50/2.75         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.50/2.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.50/2.75  thf('34', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.50/2.75      inference('sup+', [status(thm)], ['32', '33'])).
% 2.50/2.75  thf('35', plain,
% 2.50/2.75      (![X40 : $i, X41 : $i]:
% 2.50/2.75         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.50/2.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.50/2.75  thf('36', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.50/2.75      inference('sup+', [status(thm)], ['34', '35'])).
% 2.50/2.75  thf('37', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf('38', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf('39', plain,
% 2.50/2.75      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 2.50/2.75      inference('demod', [status(thm)], ['10', '11'])).
% 2.50/2.75  thf('40', plain,
% 2.50/2.75      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 2.50/2.75      inference('sup+', [status(thm)], ['38', '39'])).
% 2.50/2.75  thf('41', plain,
% 2.50/2.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['31', '36', '37', '40'])).
% 2.50/2.75  thf('42', plain,
% 2.50/2.75      (![X20 : $i, X21 : $i]:
% 2.50/2.75         ((k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21)))
% 2.50/2.75           = (X20))),
% 2.50/2.75      inference('demod', [status(thm)], ['28', '29'])).
% 2.50/2.75  thf('43', plain,
% 2.50/2.75      ((((k3_tarski @ 
% 2.50/2.75          (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.50/2.75           (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75          = (sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup+', [status(thm)], ['41', '42'])).
% 2.50/2.75  thf('44', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(t74_tops_1, axiom,
% 2.50/2.75    (![A:$i]:
% 2.50/2.75     ( ( l1_pre_topc @ A ) =>
% 2.50/2.75       ( ![B:$i]:
% 2.50/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.50/2.75           ( ( k1_tops_1 @ A @ B ) =
% 2.50/2.75             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.50/2.75  thf('45', plain,
% 2.50/2.75      (![X55 : $i, X56 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 2.50/2.75          | ((k1_tops_1 @ X56 @ X55)
% 2.50/2.75              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 2.50/2.75                 (k2_tops_1 @ X56 @ X55)))
% 2.50/2.75          | ~ (l1_pre_topc @ X56))),
% 2.50/2.75      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.50/2.75  thf('46', plain,
% 2.50/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.50/2.75        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.50/2.75            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['44', '45'])).
% 2.50/2.75  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('48', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(redefinition_k7_subset_1, axiom,
% 2.50/2.75    (![A:$i,B:$i,C:$i]:
% 2.50/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.50/2.75       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.50/2.75  thf('49', plain,
% 2.50/2.75      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 2.50/2.75          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 2.50/2.75      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.50/2.75  thf('50', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.50/2.75           = (k4_xboole_0 @ sk_B @ X0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['48', '49'])).
% 2.50/2.75  thf('51', plain,
% 2.50/2.75      (((k1_tops_1 @ sk_A @ sk_B)
% 2.50/2.75         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.50/2.75      inference('demod', [status(thm)], ['46', '47', '50'])).
% 2.50/2.75  thf('52', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf('53', plain,
% 2.50/2.75      ((((k3_tarski @ 
% 2.50/2.75          (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75          = (sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['43', '51', '52'])).
% 2.50/2.75  thf('54', plain,
% 2.50/2.75      (![X22 : $i, X23 : $i]:
% 2.50/2.75         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 2.50/2.75      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.75  thf(t3_subset, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.50/2.75  thf('55', plain,
% 2.50/2.75      (![X42 : $i, X44 : $i]:
% 2.50/2.75         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 2.50/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.50/2.75  thf('56', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         (m1_subset_1 @ X1 @ 
% 2.50/2.75          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['54', '55'])).
% 2.50/2.75  thf(d5_subset_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.50/2.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.50/2.75  thf('57', plain,
% 2.50/2.75      (![X28 : $i, X29 : $i]:
% 2.50/2.75         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 2.50/2.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 2.50/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.50/2.75  thf('58', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 2.50/2.75           = (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1))),
% 2.50/2.75      inference('sup-', [status(thm)], ['56', '57'])).
% 2.50/2.75  thf('59', plain,
% 2.50/2.75      ((((k3_subset_1 @ 
% 2.50/2.75          (k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 2.50/2.75          (k1_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup+', [status(thm)], ['53', '58'])).
% 2.50/2.75  thf('60', plain,
% 2.50/2.75      ((((k3_tarski @ 
% 2.50/2.75          (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75          = (sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['43', '51', '52'])).
% 2.50/2.75  thf('61', plain,
% 2.50/2.75      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['59', '60'])).
% 2.50/2.75  thf('62', plain,
% 2.50/2.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['31', '36', '37', '40'])).
% 2.50/2.75  thf('63', plain,
% 2.50/2.75      (![X20 : $i, X21 : $i]:
% 2.50/2.75         ((k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21)))
% 2.50/2.75           = (X20))),
% 2.50/2.75      inference('demod', [status(thm)], ['28', '29'])).
% 2.50/2.75  thf('64', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         (m1_subset_1 @ X1 @ 
% 2.50/2.75          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['54', '55'])).
% 2.50/2.75  thf('65', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.50/2.75      inference('sup+', [status(thm)], ['63', '64'])).
% 2.50/2.75  thf(involutiveness_k3_subset_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.50/2.75       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.50/2.75  thf('66', plain,
% 2.50/2.75      (![X32 : $i, X33 : $i]:
% 2.50/2.75         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 2.50/2.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 2.50/2.75      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.50/2.75  thf('67', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 2.50/2.75           = (k3_xboole_0 @ X0 @ X1))),
% 2.50/2.75      inference('sup-', [status(thm)], ['65', '66'])).
% 2.50/2.75  thf('68', plain,
% 2.50/2.75      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup+', [status(thm)], ['62', '67'])).
% 2.50/2.75  thf('69', plain,
% 2.50/2.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['31', '36', '37', '40'])).
% 2.50/2.75  thf('70', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.50/2.75      inference('sup+', [status(thm)], ['63', '64'])).
% 2.50/2.75  thf('71', plain,
% 2.50/2.75      (![X28 : $i, X29 : $i]:
% 2.50/2.75         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 2.50/2.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 2.50/2.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.50/2.75  thf('72', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.50/2.75           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['70', '71'])).
% 2.50/2.75  thf('73', plain,
% 2.50/2.75      ((((k3_subset_1 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup+', [status(thm)], ['69', '72'])).
% 2.50/2.75  thf('74', plain,
% 2.50/2.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['31', '36', '37', '40'])).
% 2.50/2.75  thf('75', plain,
% 2.50/2.75      (((k1_tops_1 @ sk_A @ sk_B)
% 2.50/2.75         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.50/2.75      inference('demod', [status(thm)], ['46', '47', '50'])).
% 2.50/2.75  thf('76', plain,
% 2.50/2.75      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k1_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.50/2.75  thf('77', plain,
% 2.50/2.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['31', '36', '37', '40'])).
% 2.50/2.75  thf('78', plain,
% 2.50/2.75      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['68', '76', '77'])).
% 2.50/2.75  thf('79', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('demod', [status(thm)], ['61', '78'])).
% 2.50/2.75  thf('80', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.50/2.75           = (k4_xboole_0 @ sk_B @ X0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['48', '49'])).
% 2.50/2.75  thf('81', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75              (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (~
% 2.50/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('split', [status(esa)], ['0'])).
% 2.50/2.75  thf('82', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= (~
% 2.50/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['80', '81'])).
% 2.50/2.75  thf('83', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.50/2.75         <= (~
% 2.50/2.75             (((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 2.50/2.75             ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['79', '82'])).
% 2.50/2.75  thf('84', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.50/2.75       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('simplify', [status(thm)], ['83'])).
% 2.50/2.75  thf('85', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.50/2.75       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('split', [status(esa)], ['2'])).
% 2.50/2.75  thf('86', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.50/2.75           = (k4_xboole_0 @ sk_B @ X0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['48', '49'])).
% 2.50/2.75  thf('87', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('split', [status(esa)], ['2'])).
% 2.50/2.75  thf('88', plain,
% 2.50/2.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.50/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('sup+', [status(thm)], ['86', '87'])).
% 2.50/2.75  thf('89', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf('90', plain,
% 2.50/2.75      (![X22 : $i, X23 : $i]:
% 2.50/2.75         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 2.50/2.75      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.75  thf('91', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('92', plain,
% 2.50/2.75      (![X42 : $i, X43 : $i]:
% 2.50/2.75         ((r1_tarski @ X42 @ X43) | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 2.50/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.50/2.75  thf('93', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.50/2.75      inference('sup-', [status(thm)], ['91', '92'])).
% 2.50/2.75  thf(t1_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i,C:$i]:
% 2.50/2.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.50/2.75       ( r1_tarski @ A @ C ) ))).
% 2.50/2.75  thf('94', plain,
% 2.50/2.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.50/2.75         (~ (r1_tarski @ X3 @ X4)
% 2.50/2.75          | ~ (r1_tarski @ X4 @ X5)
% 2.50/2.75          | (r1_tarski @ X3 @ X5))),
% 2.50/2.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.50/2.75  thf('95', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['93', '94'])).
% 2.50/2.75  thf('96', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         (r1_tarski @ sk_B @ 
% 2.50/2.75          (k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ X0)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['90', '95'])).
% 2.50/2.75  thf('97', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         (r1_tarski @ sk_B @ 
% 2.50/2.75          (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))),
% 2.50/2.75      inference('sup+', [status(thm)], ['89', '96'])).
% 2.50/2.75  thf('98', plain,
% 2.50/2.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.50/2.75         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 2.50/2.75          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 2.50/2.75      inference('demod', [status(thm)], ['13', '14'])).
% 2.50/2.75  thf('99', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 2.50/2.75      inference('sup-', [status(thm)], ['97', '98'])).
% 2.50/2.75  thf('100', plain,
% 2.50/2.75      (![X42 : $i, X44 : $i]:
% 2.50/2.75         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 2.50/2.75      inference('cnf', [status(esa)], [t3_subset])).
% 2.50/2.75  thf('101', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.50/2.75          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['99', '100'])).
% 2.50/2.75  thf('102', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(redefinition_k4_subset_1, axiom,
% 2.50/2.75    (![A:$i,B:$i,C:$i]:
% 2.50/2.75     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.50/2.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.50/2.75       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.50/2.75  thf('103', plain,
% 2.50/2.75      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 2.50/2.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 2.50/2.75          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 2.50/2.75      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.50/2.75  thf('104', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('105', plain,
% 2.50/2.75      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 2.50/2.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 2.50/2.75          | ((k4_subset_1 @ X35 @ X34 @ X36)
% 2.50/2.75              = (k3_tarski @ (k2_tarski @ X34 @ X36))))),
% 2.50/2.75      inference('demod', [status(thm)], ['103', '104'])).
% 2.50/2.75  thf('106', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.50/2.75            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 2.50/2.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['102', '105'])).
% 2.50/2.75  thf('107', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75           (k4_xboole_0 @ sk_B @ X0))
% 2.50/2.75           = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['101', '106'])).
% 2.50/2.75  thf(t36_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.50/2.75  thf('108', plain,
% 2.50/2.75      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.50/2.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.50/2.75  thf('109', plain,
% 2.50/2.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.50/2.75         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 2.50/2.75          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 2.50/2.75      inference('demod', [status(thm)], ['13', '14'])).
% 2.50/2.75  thf('110', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.75         (r1_tarski @ 
% 2.50/2.75          (k4_xboole_0 @ 
% 2.50/2.75           (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 2.50/2.75          X0)),
% 2.50/2.75      inference('sup-', [status(thm)], ['108', '109'])).
% 2.50/2.75  thf('111', plain,
% 2.50/2.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.50/2.75      inference('sup-', [status(thm)], ['24', '25'])).
% 2.50/2.75  thf('112', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k4_xboole_0 @ 
% 2.50/2.75           (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1) @ 
% 2.50/2.75           X0) = (k1_xboole_0))),
% 2.50/2.75      inference('sup-', [status(thm)], ['110', '111'])).
% 2.50/2.75  thf('113', plain,
% 2.50/2.75      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 2.50/2.75      inference('demod', [status(thm)], ['10', '11'])).
% 2.50/2.75  thf('114', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.50/2.75      inference('demod', [status(thm)], ['112', '113'])).
% 2.50/2.75  thf('115', plain,
% 2.50/2.75      (![X20 : $i, X21 : $i]:
% 2.50/2.75         ((k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21)))
% 2.50/2.75           = (X20))),
% 2.50/2.75      inference('demod', [status(thm)], ['28', '29'])).
% 2.50/2.75  thf('116', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_tarski @ 
% 2.50/2.75           (k2_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ 
% 2.50/2.75            k1_xboole_0))
% 2.50/2.75           = (k4_xboole_0 @ X1 @ X0))),
% 2.50/2.75      inference('sup+', [status(thm)], ['114', '115'])).
% 2.50/2.75  thf('117', plain,
% 2.50/2.75      (![X24 : $i, X25 : $i]:
% 2.50/2.75         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 2.50/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.50/2.75  thf('118', plain,
% 2.50/2.75      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 2.50/2.75      inference('sup+', [status(thm)], ['38', '39'])).
% 2.50/2.75  thf('119', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.50/2.75           = (k4_xboole_0 @ X1 @ X0))),
% 2.50/2.75      inference('demod', [status(thm)], ['116', '117', '118'])).
% 2.50/2.75  thf('120', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.50/2.75      inference('sup+', [status(thm)], ['34', '35'])).
% 2.50/2.75  thf('121', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.50/2.75           = (k4_xboole_0 @ X1 @ X0))),
% 2.50/2.75      inference('demod', [status(thm)], ['119', '120'])).
% 2.50/2.75  thf(t22_xboole_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 2.50/2.75  thf('122', plain,
% 2.50/2.75      (![X6 : $i, X7 : $i]:
% 2.50/2.75         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 2.50/2.75      inference('cnf', [status(esa)], [t22_xboole_1])).
% 2.50/2.75  thf('123', plain,
% 2.50/2.75      (![X26 : $i, X27 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 2.50/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.50/2.75  thf('124', plain,
% 2.50/2.75      (![X6 : $i, X7 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 2.50/2.75      inference('demod', [status(thm)], ['122', '123'])).
% 2.50/2.75  thf('125', plain,
% 2.50/2.75      (![X0 : $i, X1 : $i]:
% 2.50/2.75         ((k3_tarski @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 2.50/2.75      inference('sup+', [status(thm)], ['121', '124'])).
% 2.50/2.75  thf('126', plain,
% 2.50/2.75      (![X0 : $i]:
% 2.50/2.75         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75           (k4_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 2.50/2.75      inference('demod', [status(thm)], ['107', '125'])).
% 2.50/2.75  thf('127', plain,
% 2.50/2.75      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.50/2.75          = (sk_B)))
% 2.50/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('sup+', [status(thm)], ['88', '126'])).
% 2.50/2.75  thf('128', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(t65_tops_1, axiom,
% 2.50/2.75    (![A:$i]:
% 2.50/2.75     ( ( l1_pre_topc @ A ) =>
% 2.50/2.75       ( ![B:$i]:
% 2.50/2.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.50/2.75           ( ( k2_pre_topc @ A @ B ) =
% 2.50/2.75             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.50/2.75  thf('129', plain,
% 2.50/2.75      (![X51 : $i, X52 : $i]:
% 2.50/2.75         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 2.50/2.75          | ((k2_pre_topc @ X52 @ X51)
% 2.50/2.75              = (k4_subset_1 @ (u1_struct_0 @ X52) @ X51 @ 
% 2.50/2.75                 (k2_tops_1 @ X52 @ X51)))
% 2.50/2.75          | ~ (l1_pre_topc @ X52))),
% 2.50/2.75      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.50/2.75  thf('130', plain,
% 2.50/2.75      ((~ (l1_pre_topc @ sk_A)
% 2.50/2.75        | ((k2_pre_topc @ sk_A @ sk_B)
% 2.50/2.75            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.50/2.75      inference('sup-', [status(thm)], ['128', '129'])).
% 2.50/2.75  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('132', plain,
% 2.50/2.75      (((k2_pre_topc @ sk_A @ sk_B)
% 2.50/2.75         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.50/2.75      inference('demod', [status(thm)], ['130', '131'])).
% 2.50/2.75  thf('133', plain,
% 2.50/2.75      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.50/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('sup+', [status(thm)], ['127', '132'])).
% 2.50/2.75  thf('134', plain,
% 2.50/2.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf(fc1_tops_1, axiom,
% 2.50/2.75    (![A:$i,B:$i]:
% 2.50/2.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.50/2.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.50/2.75       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 2.50/2.75  thf('135', plain,
% 2.50/2.75      (![X47 : $i, X48 : $i]:
% 2.50/2.75         (~ (l1_pre_topc @ X47)
% 2.50/2.75          | ~ (v2_pre_topc @ X47)
% 2.50/2.75          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 2.50/2.75          | (v4_pre_topc @ (k2_pre_topc @ X47 @ X48) @ X47))),
% 2.50/2.75      inference('cnf', [status(esa)], [fc1_tops_1])).
% 2.50/2.75  thf('136', plain,
% 2.50/2.75      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.50/2.75        | ~ (v2_pre_topc @ sk_A)
% 2.50/2.75        | ~ (l1_pre_topc @ sk_A))),
% 2.50/2.75      inference('sup-', [status(thm)], ['134', '135'])).
% 2.50/2.75  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 2.50/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.75  thf('139', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.50/2.75      inference('demod', [status(thm)], ['136', '137', '138'])).
% 2.50/2.75  thf('140', plain,
% 2.50/2.75      (((v4_pre_topc @ sk_B @ sk_A))
% 2.50/2.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.50/2.75      inference('sup+', [status(thm)], ['133', '139'])).
% 2.50/2.75  thf('141', plain,
% 2.50/2.75      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.50/2.75      inference('split', [status(esa)], ['0'])).
% 2.50/2.75  thf('142', plain,
% 2.50/2.75      (~
% 2.50/2.75       (((k2_tops_1 @ sk_A @ sk_B)
% 2.50/2.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.50/2.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.50/2.75       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.50/2.75      inference('sup-', [status(thm)], ['140', '141'])).
% 2.50/2.75  thf('143', plain, ($false),
% 2.50/2.75      inference('sat_resolution*', [status(thm)], ['1', '84', '85', '142'])).
% 2.50/2.75  
% 2.50/2.75  % SZS output end Refutation
% 2.50/2.75  
% 2.50/2.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
