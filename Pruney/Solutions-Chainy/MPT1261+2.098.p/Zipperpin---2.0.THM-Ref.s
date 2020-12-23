%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZpBuny0cU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 271 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  962 (3032 expanded)
%              Number of equality atoms :   66 ( 163 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['23','28'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15','16','51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_pre_topc @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
       != X24 )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
       != ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 @ ( k2_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('82',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','82'])).

thf('84',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['63','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZpBuny0cU
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 1740 iterations in 0.716s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.17  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.17  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.99/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(t77_tops_1, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.17             ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17          ( ![B:$i]:
% 0.99/1.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17              ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.17                ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17                  ( k7_subset_1 @
% 0.99/1.17                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t3_subset, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      (![X21 : $i, X22 : $i]:
% 0.99/1.17         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('2', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf(t28_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      (![X9 : $i, X10 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('4', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf(t48_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.99/1.17           = (k3_xboole_0 @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf(t36_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.99/1.17      inference('sup+', [status(thm)], ['6', '7'])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.99/1.17      inference('sup+', [status(thm)], ['5', '8'])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X21 : $i, X23 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf(t65_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k2_pre_topc @ A @ B ) =
% 0.99/1.17             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      (![X26 : $i, X27 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.17          | ((k2_pre_topc @ X27 @ X26)
% 0.99/1.17              = (k4_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.99/1.17                 (k2_tops_1 @ X27 @ X26)))
% 0.99/1.17          | ~ (l1_pre_topc @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((k2_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 0.99/1.17              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.99/1.17                 (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 0.99/1.17                 (k2_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['11', '12'])).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k2_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup+', [status(thm)], ['4', '13'])).
% 0.99/1.17  thf('15', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('16', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k7_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.99/1.17          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['17', '20'])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.17        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('sup+', [status(thm)], ['21', '22'])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t69_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( v4_pre_topc @ B @ A ) =>
% 0.99/1.17             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.99/1.17          | (r1_tarski @ (k2_tops_1 @ X29 @ X28) @ X28)
% 0.99/1.17          | ~ (v4_pre_topc @ X28 @ X29)
% 0.99/1.17          | ~ (l1_pre_topc @ X29))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['24', '25'])).
% 0.99/1.17  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['26', '27'])).
% 0.99/1.17  thf('29', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.99/1.17      inference('clc', [status(thm)], ['23', '28'])).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X9 : $i, X10 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['31', '32'])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.99/1.17           = (k3_xboole_0 @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('35', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf(t109_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.99/1.17         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ (k4_xboole_0 @ X4 @ X6) @ X5))),
% 0.99/1.17      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (![X21 : $i, X23 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('39', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.17  thf('40', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['34', '39'])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['33', '40'])).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k4_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.99/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.99/1.17       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.99/1.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.99/1.17          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.99/1.17  thf('44', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17            = (k2_xboole_0 @ sk_B @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['41', '44'])).
% 0.99/1.17  thf('46', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.99/1.17      inference('clc', [status(thm)], ['23', '28'])).
% 0.99/1.17  thf(t12_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X7 : $i, X8 : $i]:
% 0.99/1.17         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.99/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.17  thf(commutativity_k2_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['48', '49'])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['45', '50'])).
% 0.99/1.17  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('53', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['14', '15', '16', '51', '52'])).
% 0.99/1.17  thf('54', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf(t52_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.99/1.17             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.99/1.17               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.99/1.17          | ~ (v2_pre_topc @ X25)
% 0.99/1.17          | ((k2_pre_topc @ X25 @ X24) != (X24))
% 0.99/1.17          | (v4_pre_topc @ X24 @ X25)
% 0.99/1.17          | ~ (l1_pre_topc @ X25))),
% 0.99/1.17      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | (v4_pre_topc @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.99/1.17          | ((k2_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 0.99/1.17              != (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 0.99/1.17          | ~ (v2_pre_topc @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.17          != (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['54', '57'])).
% 0.99/1.17  thf('59', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('61', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('63', plain,
% 0.99/1.17      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.99/1.17  thf('64', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17              (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('65', plain,
% 0.99/1.17      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('split', [status(esa)], ['64'])).
% 0.99/1.17  thf('66', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t74_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k1_tops_1 @ A @ B ) =
% 0.99/1.17             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('67', plain,
% 0.99/1.17      (![X30 : $i, X31 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.99/1.17          | ((k1_tops_1 @ X31 @ X30)
% 0.99/1.17              = (k7_subset_1 @ (u1_struct_0 @ X31) @ X30 @ 
% 0.99/1.17                 (k2_tops_1 @ X31 @ X30)))
% 0.99/1.17          | ~ (l1_pre_topc @ X31))),
% 0.99/1.17      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.99/1.17  thf('68', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['66', '67'])).
% 0.99/1.17  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('71', plain,
% 0.99/1.17      (((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.99/1.17           = (k3_xboole_0 @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['71', '72'])).
% 0.99/1.17  thf('74', plain,
% 0.99/1.17      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['31', '32'])).
% 0.99/1.17  thf('75', plain,
% 0.99/1.17      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('sup+', [status(thm)], ['73', '74'])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('77', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17              (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= (~
% 0.99/1.17             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('split', [status(esa)], ['64'])).
% 0.99/1.17  thf('78', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= (~
% 0.99/1.17             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['76', '77'])).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         <= (~
% 0.99/1.17             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['75', '78'])).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('simplify', [status(thm)], ['79'])).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.99/1.17       ~
% 0.99/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('split', [status(esa)], ['64'])).
% 0.99/1.17  thf('82', plain, (~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.99/1.17  thf('83', plain, (~ (v4_pre_topc @ sk_B @ sk_A)),
% 0.99/1.17      inference('simpl_trail', [status(thm)], ['65', '82'])).
% 0.99/1.17  thf('84', plain, (((k2_pre_topc @ sk_A @ sk_B) != (sk_B))),
% 0.99/1.17      inference('clc', [status(thm)], ['63', '83'])).
% 0.99/1.17  thf('85', plain, ($false),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['53', '84'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
