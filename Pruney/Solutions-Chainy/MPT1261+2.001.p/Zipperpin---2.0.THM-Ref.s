%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YVDEJzE4gV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 839 expanded)
%              Number of leaves         :   48 ( 286 expanded)
%              Depth                    :   20
%              Number of atoms          : 1883 (8774 expanded)
%              Number of equality atoms :  134 ( 586 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('10',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X66 @ X65 ) @ X65 )
      | ~ ( v4_pre_topc @ X65 @ X66 )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','33','34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('40',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( ( k1_tops_1 @ X68 @ X67 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X68 ) @ X67 @ ( k2_tops_1 @ X68 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','58'])).

thf('60',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('61',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('64',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X40 @ ( k3_subset_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('74',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('85',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k2_pre_topc @ X64 @ X63 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('94',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('109',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k4_subset_1 @ X45 @ X44 @ X46 )
        = ( k2_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X1 )
        = ( k2_xboole_0 @ sk_B @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('120',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('126',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('127',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('130',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('132',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('136',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('137',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('141',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['135','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','142'])).

thf('144',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['125','145'])).

thf('147',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('148',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('151',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','124','151'])).

thf('153',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('155',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( l1_pre_topc @ X59 )
      | ~ ( v2_pre_topc @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X59 @ X60 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('156',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['153','159'])).

thf('161',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','82','83','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YVDEJzE4gV
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.75  % Solved by: fo/fo7.sh
% 1.49/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.75  % done 4183 iterations in 1.301s
% 1.49/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.75  % SZS output start Refutation
% 1.49/1.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.75  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.49/1.75  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.49/1.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.49/1.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.49/1.75  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.49/1.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.49/1.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.49/1.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.75  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.49/1.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.49/1.75  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.49/1.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.75  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.49/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.49/1.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.49/1.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.49/1.75  thf(t77_tops_1, conjecture,
% 1.49/1.75    (![A:$i]:
% 1.49/1.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.75       ( ![B:$i]:
% 1.49/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.75           ( ( v4_pre_topc @ B @ A ) <=>
% 1.49/1.75             ( ( k2_tops_1 @ A @ B ) =
% 1.49/1.75               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.49/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.75    (~( ![A:$i]:
% 1.49/1.75        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.75          ( ![B:$i]:
% 1.49/1.75            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.75              ( ( v4_pre_topc @ B @ A ) <=>
% 1.49/1.75                ( ( k2_tops_1 @ A @ B ) =
% 1.49/1.75                  ( k7_subset_1 @
% 1.49/1.75                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.49/1.75    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.49/1.75  thf('0', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75              (k1_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('1', plain,
% 1.49/1.75      (~
% 1.49/1.75       (((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.49/1.75       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.75      inference('split', [status(esa)], ['0'])).
% 1.49/1.75  thf(commutativity_k2_xboole_0, axiom,
% 1.49/1.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.49/1.75  thf('2', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf(t36_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.49/1.75  thf('3', plain,
% 1.49/1.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.49/1.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.75  thf(t44_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.49/1.75       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.49/1.75  thf('4', plain,
% 1.49/1.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.49/1.75         ((r1_tarski @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 1.49/1.75          | ~ (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X26))),
% 1.49/1.75      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.49/1.75  thf('5', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.75  thf('6', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['2', '5'])).
% 1.49/1.75  thf('7', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75             (k1_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('8', plain,
% 1.49/1.75      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('split', [status(esa)], ['7'])).
% 1.49/1.75  thf('9', plain,
% 1.49/1.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(t69_tops_1, axiom,
% 1.49/1.75    (![A:$i]:
% 1.49/1.75     ( ( l1_pre_topc @ A ) =>
% 1.49/1.75       ( ![B:$i]:
% 1.49/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.75           ( ( v4_pre_topc @ B @ A ) =>
% 1.49/1.75             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.49/1.75  thf('10', plain,
% 1.49/1.75      (![X65 : $i, X66 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 1.49/1.75          | (r1_tarski @ (k2_tops_1 @ X66 @ X65) @ X65)
% 1.49/1.75          | ~ (v4_pre_topc @ X65 @ X66)
% 1.49/1.75          | ~ (l1_pre_topc @ X66))),
% 1.49/1.75      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.49/1.75  thf('11', plain,
% 1.49/1.75      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.75        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.49/1.75        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.49/1.75      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.75  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('13', plain,
% 1.49/1.75      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.49/1.75        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.49/1.75      inference('demod', [status(thm)], ['11', '12'])).
% 1.49/1.75  thf('14', plain,
% 1.49/1.75      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['8', '13'])).
% 1.49/1.75  thf(t1_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.49/1.75       ( r1_tarski @ A @ C ) ))).
% 1.49/1.75  thf('15', plain,
% 1.49/1.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.49/1.75         (~ (r1_tarski @ X10 @ X11)
% 1.49/1.75          | ~ (r1_tarski @ X11 @ X12)
% 1.49/1.75          | (r1_tarski @ X10 @ X12))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.49/1.75  thf('16', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.49/1.75           | ~ (r1_tarski @ sk_B @ X0)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['14', '15'])).
% 1.49/1.75  thf('17', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['6', '16'])).
% 1.49/1.75  thf(t43_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.49/1.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.49/1.75  thf('18', plain,
% 1.49/1.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.49/1.75         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.49/1.75          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.49/1.75  thf('19', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['17', '18'])).
% 1.49/1.75  thf(t38_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.49/1.75       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.49/1.75  thf('20', plain,
% 1.49/1.75      (![X17 : $i, X18 : $i]:
% 1.49/1.75         (((X17) = (k1_xboole_0))
% 1.49/1.75          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.49/1.75  thf('21', plain,
% 1.49/1.75      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['19', '20'])).
% 1.49/1.75  thf(t47_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.49/1.75  thf('22', plain,
% 1.49/1.75      (![X27 : $i, X28 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 1.49/1.75           = (k4_xboole_0 @ X27 @ X28))),
% 1.49/1.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.49/1.75  thf(t39_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.49/1.75  thf('23', plain,
% 1.49/1.75      (![X19 : $i, X20 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 1.49/1.75           = (k2_xboole_0 @ X19 @ X20))),
% 1.49/1.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.49/1.75  thf('24', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.75           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.49/1.75      inference('sup+', [status(thm)], ['22', '23'])).
% 1.49/1.75  thf('25', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf(t22_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.49/1.75  thf('26', plain,
% 1.49/1.75      (![X13 : $i, X14 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) = (X13))),
% 1.49/1.75      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.49/1.75  thf('27', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.75           = (X1))),
% 1.49/1.75      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.49/1.75  thf('28', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.49/1.75          k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['21', '27'])).
% 1.49/1.75  thf(commutativity_k2_tarski, axiom,
% 1.49/1.75    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.49/1.75  thf('29', plain,
% 1.49/1.75      (![X32 : $i, X33 : $i]:
% 1.49/1.75         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.49/1.75  thf(t12_setfam_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.49/1.75  thf('30', plain,
% 1.49/1.75      (![X52 : $i, X53 : $i]:
% 1.49/1.75         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 1.49/1.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.49/1.75  thf('31', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('sup+', [status(thm)], ['29', '30'])).
% 1.49/1.75  thf('32', plain,
% 1.49/1.75      (![X52 : $i, X53 : $i]:
% 1.49/1.75         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 1.49/1.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.49/1.75  thf('33', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('sup+', [status(thm)], ['31', '32'])).
% 1.49/1.75  thf('34', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('35', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf(t1_boole, axiom,
% 1.49/1.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.49/1.75  thf('36', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_boole])).
% 1.49/1.75  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['35', '36'])).
% 1.49/1.75  thf('38', plain,
% 1.49/1.75      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['28', '33', '34', '37'])).
% 1.49/1.75  thf('39', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.49/1.75           = (X1))),
% 1.49/1.75      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.49/1.75  thf('40', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.49/1.75          (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['38', '39'])).
% 1.49/1.75  thf('41', plain,
% 1.49/1.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(t74_tops_1, axiom,
% 1.49/1.75    (![A:$i]:
% 1.49/1.75     ( ( l1_pre_topc @ A ) =>
% 1.49/1.75       ( ![B:$i]:
% 1.49/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.75           ( ( k1_tops_1 @ A @ B ) =
% 1.49/1.75             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.49/1.75  thf('42', plain,
% 1.49/1.75      (![X67 : $i, X68 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 1.49/1.75          | ((k1_tops_1 @ X68 @ X67)
% 1.49/1.75              = (k7_subset_1 @ (u1_struct_0 @ X68) @ X67 @ 
% 1.49/1.75                 (k2_tops_1 @ X68 @ X67)))
% 1.49/1.75          | ~ (l1_pre_topc @ X68))),
% 1.49/1.75      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.49/1.75  thf('43', plain,
% 1.49/1.75      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.75        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.49/1.75            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['41', '42'])).
% 1.49/1.75  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('45', plain,
% 1.49/1.75      (((k1_tops_1 @ sk_A @ sk_B)
% 1.49/1.75         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.49/1.75      inference('demod', [status(thm)], ['43', '44'])).
% 1.49/1.75  thf('46', plain,
% 1.49/1.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(redefinition_k7_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.49/1.75  thf('47', plain,
% 1.49/1.75      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 1.49/1.75          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 1.49/1.75      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.49/1.75  thf('48', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.49/1.75           = (k4_xboole_0 @ sk_B @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['46', '47'])).
% 1.49/1.75  thf('49', plain,
% 1.49/1.75      (((k1_tops_1 @ sk_A @ sk_B)
% 1.49/1.75         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.49/1.75      inference('demod', [status(thm)], ['45', '48'])).
% 1.49/1.75  thf('50', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('51', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('52', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('53', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.75  thf(t3_subset, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.49/1.75  thf('54', plain,
% 1.49/1.75      (![X54 : $i, X56 : $i]:
% 1.49/1.75         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 1.49/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.75  thf('55', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['53', '54'])).
% 1.49/1.75  thf('56', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['52', '55'])).
% 1.49/1.75  thf(d5_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.49/1.75  thf('57', plain,
% 1.49/1.75      (![X35 : $i, X36 : $i]:
% 1.49/1.75         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 1.49/1.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 1.49/1.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.49/1.75  thf('58', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.49/1.75           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.49/1.75      inference('sup-', [status(thm)], ['56', '57'])).
% 1.49/1.75  thf('59', plain,
% 1.49/1.75      ((((k3_subset_1 @ 
% 1.49/1.75          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.49/1.75          (k1_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['51', '58'])).
% 1.49/1.75  thf('60', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('61', plain,
% 1.49/1.75      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['59', '60'])).
% 1.49/1.75  thf('62', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('63', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['53', '54'])).
% 1.49/1.75  thf(involutiveness_k3_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.49/1.75       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.49/1.75  thf('64', plain,
% 1.49/1.75      (![X39 : $i, X40 : $i]:
% 1.49/1.75         (((k3_subset_1 @ X40 @ (k3_subset_1 @ X40 @ X39)) = (X39))
% 1.49/1.75          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 1.49/1.75      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.49/1.75  thf('65', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.49/1.75           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['63', '64'])).
% 1.49/1.75  thf('66', plain,
% 1.49/1.75      ((((k3_subset_1 @ sk_B @ 
% 1.49/1.75          (k3_subset_1 @ 
% 1.49/1.75           (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.49/1.75           (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['62', '65'])).
% 1.49/1.75  thf('67', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('68', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('69', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['53', '54'])).
% 1.49/1.75  thf('70', plain,
% 1.49/1.75      (![X35 : $i, X36 : $i]:
% 1.49/1.75         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 1.49/1.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 1.49/1.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.49/1.75  thf('71', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.49/1.75           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['69', '70'])).
% 1.49/1.75  thf('72', plain,
% 1.49/1.75      ((((k3_subset_1 @ 
% 1.49/1.75          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.49/1.75          (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup+', [status(thm)], ['68', '71'])).
% 1.49/1.75  thf('73', plain,
% 1.49/1.75      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['40', '49', '50'])).
% 1.49/1.75  thf('74', plain,
% 1.49/1.75      (((k1_tops_1 @ sk_A @ sk_B)
% 1.49/1.75         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.49/1.75      inference('demod', [status(thm)], ['45', '48'])).
% 1.49/1.75  thf('75', plain,
% 1.49/1.75      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.49/1.75  thf('76', plain,
% 1.49/1.75      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['66', '67', '75'])).
% 1.49/1.75  thf('77', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['61', '76'])).
% 1.49/1.75  thf('78', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.49/1.75           = (k4_xboole_0 @ sk_B @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['46', '47'])).
% 1.49/1.75  thf('79', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75              (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (~
% 1.49/1.75             (((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('split', [status(esa)], ['0'])).
% 1.49/1.75  thf('80', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= (~
% 1.49/1.75             (((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['78', '79'])).
% 1.49/1.75  thf('81', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.49/1.75         <= (~
% 1.49/1.75             (((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.49/1.75             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['77', '80'])).
% 1.49/1.75  thf('82', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.49/1.75       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.75      inference('simplify', [status(thm)], ['81'])).
% 1.49/1.75  thf('83', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.49/1.75       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.75      inference('split', [status(esa)], ['7'])).
% 1.49/1.75  thf('84', plain,
% 1.49/1.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf(t65_tops_1, axiom,
% 1.49/1.75    (![A:$i]:
% 1.49/1.75     ( ( l1_pre_topc @ A ) =>
% 1.49/1.75       ( ![B:$i]:
% 1.49/1.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.75           ( ( k2_pre_topc @ A @ B ) =
% 1.49/1.75             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.49/1.75  thf('85', plain,
% 1.49/1.75      (![X63 : $i, X64 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 1.49/1.75          | ((k2_pre_topc @ X64 @ X63)
% 1.49/1.75              = (k4_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 1.49/1.75                 (k2_tops_1 @ X64 @ X63)))
% 1.49/1.75          | ~ (l1_pre_topc @ X64))),
% 1.49/1.75      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.49/1.75  thf('86', plain,
% 1.49/1.75      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.75        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.49/1.75            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['84', '85'])).
% 1.49/1.75  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('88', plain,
% 1.49/1.75      (((k2_pre_topc @ sk_A @ sk_B)
% 1.49/1.75         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.49/1.75      inference('demod', [status(thm)], ['86', '87'])).
% 1.49/1.75  thf('89', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['2', '5'])).
% 1.49/1.75  thf('90', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.49/1.75           = (k4_xboole_0 @ sk_B @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['46', '47'])).
% 1.49/1.75  thf('91', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75             (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('split', [status(esa)], ['7'])).
% 1.49/1.75  thf('92', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup+', [status(thm)], ['90', '91'])).
% 1.49/1.75  thf('93', plain,
% 1.49/1.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.49/1.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.75  thf('94', plain,
% 1.49/1.75      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup+', [status(thm)], ['92', '93'])).
% 1.49/1.75  thf('95', plain,
% 1.49/1.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.49/1.75         (~ (r1_tarski @ X10 @ X11)
% 1.49/1.75          | ~ (r1_tarski @ X11 @ X12)
% 1.49/1.75          | (r1_tarski @ X10 @ X12))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.49/1.75  thf('96', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.49/1.75           | ~ (r1_tarski @ sk_B @ X0)))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['94', '95'])).
% 1.49/1.75  thf('97', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['89', '96'])).
% 1.49/1.75  thf('98', plain,
% 1.49/1.75      (![X54 : $i, X56 : $i]:
% 1.49/1.75         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 1.49/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.75  thf('99', plain,
% 1.49/1.75      ((![X0 : $i]:
% 1.49/1.75          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.49/1.75           (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B @ X0))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['97', '98'])).
% 1.49/1.75  thf('100', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.75  thf('101', plain,
% 1.49/1.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('102', plain,
% 1.49/1.75      (![X54 : $i, X55 : $i]:
% 1.49/1.75         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.75  thf('103', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.49/1.75      inference('sup-', [status(thm)], ['101', '102'])).
% 1.49/1.75  thf('104', plain,
% 1.49/1.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.49/1.75         (~ (r1_tarski @ X10 @ X11)
% 1.49/1.75          | ~ (r1_tarski @ X11 @ X12)
% 1.49/1.75          | (r1_tarski @ X10 @ X12))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.49/1.75  thf('105', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['103', '104'])).
% 1.49/1.75  thf('106', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['100', '105'])).
% 1.49/1.75  thf('107', plain,
% 1.49/1.75      (![X54 : $i, X56 : $i]:
% 1.49/1.75         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 1.49/1.75      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.75  thf('108', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (m1_subset_1 @ sk_B @ 
% 1.49/1.75          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['106', '107'])).
% 1.49/1.75  thf(redefinition_k4_subset_1, axiom,
% 1.49/1.75    (![A:$i,B:$i,C:$i]:
% 1.49/1.75     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.49/1.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.49/1.75       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.49/1.75  thf('109', plain,
% 1.49/1.75      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.49/1.75         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.49/1.75          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45))
% 1.49/1.75          | ((k4_subset_1 @ X45 @ X44 @ X46) = (k2_xboole_0 @ X44 @ X46)))),
% 1.49/1.75      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.49/1.75  thf('110', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         (((k4_subset_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B @ X1)
% 1.49/1.75            = (k2_xboole_0 @ sk_B @ X1))
% 1.49/1.75          | ~ (m1_subset_1 @ X1 @ 
% 1.49/1.75               (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['108', '109'])).
% 1.49/1.75  thf('111', plain,
% 1.49/1.75      ((((k4_subset_1 @ (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 1.49/1.75          (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.75          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup-', [status(thm)], ['99', '110'])).
% 1.49/1.75  thf('112', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('113', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['100', '105'])).
% 1.49/1.75  thf('114', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['112', '113'])).
% 1.49/1.75  thf('115', plain,
% 1.49/1.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.49/1.75         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.49/1.75          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.49/1.75  thf('116', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 1.49/1.75      inference('sup-', [status(thm)], ['114', '115'])).
% 1.49/1.75  thf('117', plain,
% 1.49/1.75      (![X17 : $i, X18 : $i]:
% 1.49/1.75         (((X17) = (k1_xboole_0))
% 1.49/1.75          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.49/1.75  thf('118', plain,
% 1.49/1.75      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['116', '117'])).
% 1.49/1.75  thf('119', plain,
% 1.49/1.75      (![X19 : $i, X20 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 1.49/1.75           = (k2_xboole_0 @ X19 @ X20))),
% 1.49/1.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.49/1.75  thf('120', plain,
% 1.49/1.75      (((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.49/1.75         = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.49/1.75      inference('sup+', [status(thm)], ['118', '119'])).
% 1.49/1.75  thf('121', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('122', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['35', '36'])).
% 1.49/1.75  thf('123', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('124', plain,
% 1.49/1.75      (((u1_struct_0 @ sk_A) = (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.49/1.75      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 1.49/1.75  thf('125', plain,
% 1.49/1.75      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup+', [status(thm)], ['90', '91'])).
% 1.49/1.75  thf('126', plain,
% 1.49/1.75      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.49/1.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.75  thf('127', plain,
% 1.49/1.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.49/1.75         ((r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 1.49/1.75          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.49/1.75  thf('128', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.75         (r1_tarski @ 
% 1.49/1.75          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 1.49/1.75          X0)),
% 1.49/1.75      inference('sup-', [status(thm)], ['126', '127'])).
% 1.49/1.75  thf('129', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['35', '36'])).
% 1.49/1.75  thf('130', plain,
% 1.49/1.75      (![X13 : $i, X14 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) = (X13))),
% 1.49/1.75      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.49/1.75  thf('131', plain,
% 1.49/1.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['129', '130'])).
% 1.49/1.75  thf(t100_xboole_1, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.49/1.75  thf('132', plain,
% 1.49/1.75      (![X7 : $i, X8 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ X7 @ X8)
% 1.49/1.75           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.49/1.75  thf('133', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.75           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.49/1.75      inference('sup+', [status(thm)], ['131', '132'])).
% 1.49/1.75  thf('134', plain,
% 1.49/1.75      (![X17 : $i, X18 : $i]:
% 1.49/1.75         (((X17) = (k1_xboole_0))
% 1.49/1.75          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.49/1.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.49/1.75  thf('135', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.49/1.75          | ((X0) = (k1_xboole_0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['133', '134'])).
% 1.49/1.75  thf(d3_tarski, axiom,
% 1.49/1.75    (![A:$i,B:$i]:
% 1.49/1.75     ( ( r1_tarski @ A @ B ) <=>
% 1.49/1.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.49/1.75  thf('136', plain,
% 1.49/1.75      (![X3 : $i, X5 : $i]:
% 1.49/1.75         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.49/1.75      inference('cnf', [status(esa)], [d3_tarski])).
% 1.49/1.75  thf('137', plain,
% 1.49/1.75      (![X3 : $i, X5 : $i]:
% 1.49/1.75         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.49/1.75      inference('cnf', [status(esa)], [d3_tarski])).
% 1.49/1.75  thf('138', plain,
% 1.49/1.75      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['136', '137'])).
% 1.49/1.75  thf('139', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.49/1.75      inference('simplify', [status(thm)], ['138'])).
% 1.49/1.75  thf('140', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.49/1.75          | ((X0) = (k1_xboole_0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['133', '134'])).
% 1.49/1.75  thf('141', plain,
% 1.49/1.75      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['139', '140'])).
% 1.49/1.75  thf('142', plain,
% 1.49/1.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.49/1.75      inference('demod', [status(thm)], ['135', '141'])).
% 1.49/1.75  thf('143', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ 
% 1.49/1.75           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1) @ X0)
% 1.49/1.75           = (k1_xboole_0))),
% 1.49/1.75      inference('sup-', [status(thm)], ['128', '142'])).
% 1.49/1.75  thf('144', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.49/1.75      inference('cnf', [status(esa)], [t1_boole])).
% 1.49/1.75  thf('145', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]:
% 1.49/1.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.49/1.75      inference('demod', [status(thm)], ['143', '144'])).
% 1.49/1.75  thf('146', plain,
% 1.49/1.75      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup+', [status(thm)], ['125', '145'])).
% 1.49/1.75  thf('147', plain,
% 1.49/1.75      (![X19 : $i, X20 : $i]:
% 1.49/1.75         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 1.49/1.75           = (k2_xboole_0 @ X19 @ X20))),
% 1.49/1.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.49/1.75  thf('148', plain,
% 1.49/1.75      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.49/1.75          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.49/1.75         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.75                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.75                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.75      inference('sup+', [status(thm)], ['146', '147'])).
% 1.49/1.75  thf('149', plain,
% 1.49/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.49/1.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.49/1.75  thf('150', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.49/1.76      inference('sup+', [status(thm)], ['35', '36'])).
% 1.49/1.76  thf('151', plain,
% 1.49/1.76      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.49/1.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.76      inference('demod', [status(thm)], ['148', '149', '150'])).
% 1.49/1.76  thf('152', plain,
% 1.49/1.76      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.49/1.76          = (sk_B)))
% 1.49/1.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.76      inference('demod', [status(thm)], ['111', '124', '151'])).
% 1.49/1.76  thf('153', plain,
% 1.49/1.76      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.49/1.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.76      inference('sup+', [status(thm)], ['88', '152'])).
% 1.49/1.76  thf('154', plain,
% 1.49/1.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.76  thf(fc1_tops_1, axiom,
% 1.49/1.76    (![A:$i,B:$i]:
% 1.49/1.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.49/1.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.49/1.76       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.49/1.76  thf('155', plain,
% 1.49/1.76      (![X59 : $i, X60 : $i]:
% 1.49/1.76         (~ (l1_pre_topc @ X59)
% 1.49/1.76          | ~ (v2_pre_topc @ X59)
% 1.49/1.76          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 1.49/1.76          | (v4_pre_topc @ (k2_pre_topc @ X59 @ X60) @ X59))),
% 1.49/1.76      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.49/1.76  thf('156', plain,
% 1.49/1.76      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.49/1.76        | ~ (v2_pre_topc @ sk_A)
% 1.49/1.76        | ~ (l1_pre_topc @ sk_A))),
% 1.49/1.76      inference('sup-', [status(thm)], ['154', '155'])).
% 1.49/1.76  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 1.49/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.76  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.76  thf('159', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.49/1.76      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.49/1.76  thf('160', plain,
% 1.49/1.76      (((v4_pre_topc @ sk_B @ sk_A))
% 1.49/1.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.49/1.76      inference('sup+', [status(thm)], ['153', '159'])).
% 1.49/1.76  thf('161', plain,
% 1.49/1.76      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.49/1.76      inference('split', [status(esa)], ['0'])).
% 1.49/1.76  thf('162', plain,
% 1.49/1.76      (~
% 1.49/1.76       (((k2_tops_1 @ sk_A @ sk_B)
% 1.49/1.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.49/1.76             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.49/1.76       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.49/1.76      inference('sup-', [status(thm)], ['160', '161'])).
% 1.49/1.76  thf('163', plain, ($false),
% 1.49/1.76      inference('sat_resolution*', [status(thm)], ['1', '82', '83', '162'])).
% 1.49/1.76  
% 1.49/1.76  % SZS output end Refutation
% 1.49/1.76  
% 1.49/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
