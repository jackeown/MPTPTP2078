%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hWQSNp7RLr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 582 expanded)
%              Number of leaves         :   39 ( 182 expanded)
%              Depth                    :   22
%              Number of atoms          : 1629 (7479 expanded)
%              Number of equality atoms :  125 ( 451 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k1_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X39 @ X38 ) @ X38 )
      | ~ ( v4_pre_topc @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['16','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_pre_topc @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
       != X32 )
      | ( v4_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['16','21'])).

thf('48',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['32'])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('86',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('88',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('92',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','90','91'])).

thf('93',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['32'])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('99',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','103'])).

thf('105',plain,
    ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','104'])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('107',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('110',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = ( k2_subset_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('111',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('112',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X26 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('115',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('124',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['113','128'])).

thf('130',plain,
    ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['106','129'])).

thf('131',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('132',plain,
    ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['105','132'])).

thf('134',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['41','133'])).

thf('135',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['35','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hWQSNp7RLr
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.05/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.31  % Solved by: fo/fo7.sh
% 1.05/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.31  % done 2225 iterations in 0.876s
% 1.05/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.31  % SZS output start Refutation
% 1.05/1.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.05/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.31  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.05/1.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.31  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.05/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.05/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.05/1.31  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.05/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.31  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.05/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.31  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.05/1.31  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.05/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.31  thf(t77_tops_1, conjecture,
% 1.05/1.31    (![A:$i]:
% 1.05/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.31       ( ![B:$i]:
% 1.05/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31           ( ( v4_pre_topc @ B @ A ) <=>
% 1.05/1.31             ( ( k2_tops_1 @ A @ B ) =
% 1.05/1.31               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.31    (~( ![A:$i]:
% 1.05/1.31        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.31          ( ![B:$i]:
% 1.05/1.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31              ( ( v4_pre_topc @ B @ A ) <=>
% 1.05/1.31                ( ( k2_tops_1 @ A @ B ) =
% 1.05/1.31                  ( k7_subset_1 @
% 1.05/1.31                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.05/1.31    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.05/1.31  thf('0', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31              (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('1', plain,
% 1.05/1.31      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.31      inference('split', [status(esa)], ['0'])).
% 1.05/1.31  thf('2', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(t74_tops_1, axiom,
% 1.05/1.31    (![A:$i]:
% 1.05/1.31     ( ( l1_pre_topc @ A ) =>
% 1.05/1.31       ( ![B:$i]:
% 1.05/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31           ( ( k1_tops_1 @ A @ B ) =
% 1.05/1.31             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.31  thf('3', plain,
% 1.05/1.31      (![X40 : $i, X41 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.05/1.31          | ((k1_tops_1 @ X41 @ X40)
% 1.05/1.31              = (k7_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 1.05/1.31                 (k2_tops_1 @ X41 @ X40)))
% 1.05/1.31          | ~ (l1_pre_topc @ X41))),
% 1.05/1.31      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.05/1.31  thf('4', plain,
% 1.05/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.31        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.05/1.31            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.31  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('6', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(redefinition_k7_subset_1, axiom,
% 1.05/1.31    (![A:$i,B:$i,C:$i]:
% 1.05/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.31       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.05/1.31  thf('7', plain,
% 1.05/1.31      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.05/1.31          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.05/1.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.05/1.31  thf('8', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.31           = (k4_xboole_0 @ sk_B @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.31  thf('9', plain,
% 1.05/1.31      (((k1_tops_1 @ sk_A @ sk_B)
% 1.05/1.31         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.05/1.31  thf(t48_xboole_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.31  thf('10', plain,
% 1.05/1.31      (![X12 : $i, X13 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.05/1.31           = (k3_xboole_0 @ X12 @ X13))),
% 1.05/1.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.31  thf('11', plain,
% 1.05/1.31      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.31  thf('12', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('13', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.31           = (k4_xboole_0 @ sk_B @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.31  thf('14', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('demod', [status(thm)], ['12', '13'])).
% 1.05/1.31  thf(t36_xboole_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.05/1.31  thf('15', plain,
% 1.05/1.31      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.05/1.31      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.31  thf('16', plain,
% 1.05/1.31      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.31        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('sup+', [status(thm)], ['14', '15'])).
% 1.05/1.31  thf('17', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(t69_tops_1, axiom,
% 1.05/1.31    (![A:$i]:
% 1.05/1.31     ( ( l1_pre_topc @ A ) =>
% 1.05/1.31       ( ![B:$i]:
% 1.05/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31           ( ( v4_pre_topc @ B @ A ) =>
% 1.05/1.31             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.05/1.31  thf('18', plain,
% 1.05/1.31      (![X38 : $i, X39 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.05/1.31          | (r1_tarski @ (k2_tops_1 @ X39 @ X38) @ X38)
% 1.05/1.31          | ~ (v4_pre_topc @ X38 @ X39)
% 1.05/1.31          | ~ (l1_pre_topc @ X39))),
% 1.05/1.31      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.05/1.31  thf('19', plain,
% 1.05/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.31        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.05/1.31        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.05/1.31      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.31  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('21', plain,
% 1.05/1.31      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.05/1.31        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['19', '20'])).
% 1.05/1.31  thf('22', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.05/1.31      inference('clc', [status(thm)], ['16', '21'])).
% 1.05/1.31  thf(t28_xboole_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.31  thf('23', plain,
% 1.05/1.31      (![X6 : $i, X7 : $i]:
% 1.05/1.31         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.31  thf('24', plain,
% 1.05/1.31      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.31         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('sup-', [status(thm)], ['22', '23'])).
% 1.05/1.31  thf(commutativity_k3_xboole_0, axiom,
% 1.05/1.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.05/1.31  thf('25', plain,
% 1.05/1.31      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.31  thf('26', plain,
% 1.05/1.31      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.31  thf('27', plain,
% 1.05/1.31      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('sup+', [status(thm)], ['11', '26'])).
% 1.05/1.31  thf('28', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.31           = (k4_xboole_0 @ sk_B @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.31  thf('29', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31              (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= (~
% 1.05/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('split', [status(esa)], ['0'])).
% 1.05/1.31  thf('30', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= (~
% 1.05/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup-', [status(thm)], ['28', '29'])).
% 1.05/1.31  thf('31', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31         <= (~
% 1.05/1.31             (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup-', [status(thm)], ['27', '30'])).
% 1.05/1.31  thf('32', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('simplify', [status(thm)], ['31'])).
% 1.05/1.31  thf('33', plain,
% 1.05/1.31      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.05/1.31       ~
% 1.05/1.31       (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('split', [status(esa)], ['0'])).
% 1.05/1.31  thf('34', plain, (~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 1.05/1.31  thf('35', plain, (~ (v4_pre_topc @ sk_B @ sk_A)),
% 1.05/1.31      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 1.05/1.31  thf('36', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(t52_pre_topc, axiom,
% 1.05/1.31    (![A:$i]:
% 1.05/1.31     ( ( l1_pre_topc @ A ) =>
% 1.05/1.31       ( ![B:$i]:
% 1.05/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.05/1.31             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.05/1.31               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.05/1.31  thf('37', plain,
% 1.05/1.31      (![X32 : $i, X33 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.05/1.31          | ~ (v2_pre_topc @ X33)
% 1.05/1.31          | ((k2_pre_topc @ X33 @ X32) != (X32))
% 1.05/1.31          | (v4_pre_topc @ X32 @ X33)
% 1.05/1.31          | ~ (l1_pre_topc @ X33))),
% 1.05/1.31      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.05/1.31  thf('38', plain,
% 1.05/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.31        | (v4_pre_topc @ sk_B @ sk_A)
% 1.05/1.31        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.05/1.31        | ~ (v2_pre_topc @ sk_A))),
% 1.05/1.31      inference('sup-', [status(thm)], ['36', '37'])).
% 1.05/1.31  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('41', plain,
% 1.05/1.31      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.05/1.31  thf('42', plain,
% 1.05/1.31      (((k1_tops_1 @ sk_A @ sk_B)
% 1.05/1.31         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.05/1.31  thf('43', plain,
% 1.05/1.31      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.05/1.31      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.31  thf(t3_subset, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.05/1.31  thf('44', plain,
% 1.05/1.31      (![X29 : $i, X31 : $i]:
% 1.05/1.31         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 1.05/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.31  thf('45', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['43', '44'])).
% 1.05/1.31  thf('46', plain,
% 1.05/1.31      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.05/1.31      inference('sup+', [status(thm)], ['42', '45'])).
% 1.05/1.31  thf('47', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.05/1.31      inference('clc', [status(thm)], ['16', '21'])).
% 1.05/1.31  thf('48', plain,
% 1.05/1.31      (![X29 : $i, X31 : $i]:
% 1.05/1.31         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X29 @ X31))),
% 1.05/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.31  thf('49', plain,
% 1.05/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.05/1.31      inference('sup-', [status(thm)], ['47', '48'])).
% 1.05/1.31  thf(redefinition_k4_subset_1, axiom,
% 1.05/1.31    (![A:$i,B:$i,C:$i]:
% 1.05/1.31     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.31       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.31  thf('50', plain,
% 1.05/1.31      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.05/1.31          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 1.05/1.31          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 1.05/1.31      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.31  thf('51', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.05/1.31            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.05/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.05/1.31      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.31  thf('52', plain,
% 1.05/1.31      (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31         (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('sup-', [status(thm)], ['46', '51'])).
% 1.05/1.31  thf(commutativity_k2_xboole_0, axiom,
% 1.05/1.31    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.05/1.31  thf('53', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('54', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.31           = (k4_xboole_0 @ sk_B @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.31  thf('55', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('56', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('split', [status(esa)], ['55'])).
% 1.05/1.31  thf('57', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup+', [status(thm)], ['54', '56'])).
% 1.05/1.31  thf(t39_xboole_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.31  thf('58', plain,
% 1.05/1.31      (![X10 : $i, X11 : $i]:
% 1.05/1.31         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.05/1.31           = (k2_xboole_0 @ X10 @ X11))),
% 1.05/1.31      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.31  thf('59', plain,
% 1.05/1.31      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup+', [status(thm)], ['57', '58'])).
% 1.05/1.31  thf('60', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('61', plain,
% 1.05/1.31      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31          = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('demod', [status(thm)], ['59', '60'])).
% 1.05/1.31  thf('62', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('sat_resolution*', [status(thm)], ['32'])).
% 1.05/1.31  thf('63', plain,
% 1.05/1.31      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 1.05/1.31  thf('64', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(dt_k2_tops_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( ( l1_pre_topc @ A ) & 
% 1.05/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.31       ( m1_subset_1 @
% 1.05/1.31         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.05/1.31  thf('65', plain,
% 1.05/1.31      (![X34 : $i, X35 : $i]:
% 1.05/1.31         (~ (l1_pre_topc @ X34)
% 1.05/1.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.05/1.31          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 1.05/1.31             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 1.05/1.31      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.05/1.31  thf('66', plain,
% 1.05/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.31      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.31  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('68', plain,
% 1.05/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('demod', [status(thm)], ['66', '67'])).
% 1.05/1.31  thf('69', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('70', plain,
% 1.05/1.31      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.05/1.31          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 1.05/1.31          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 1.05/1.31      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.31  thf('71', plain,
% 1.05/1.31      (![X0 : $i]:
% 1.05/1.31         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.31            = (k2_xboole_0 @ sk_B @ X0))
% 1.05/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.31      inference('sup-', [status(thm)], ['69', '70'])).
% 1.05/1.31  thf('72', plain,
% 1.05/1.31      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('sup-', [status(thm)], ['68', '71'])).
% 1.05/1.31  thf('73', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup+', [status(thm)], ['54', '56'])).
% 1.05/1.31  thf('74', plain,
% 1.05/1.31      (![X12 : $i, X13 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.05/1.31           = (k3_xboole_0 @ X12 @ X13))),
% 1.05/1.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.31  thf('75', plain,
% 1.05/1.31      (![X10 : $i, X11 : $i]:
% 1.05/1.31         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.05/1.31           = (k2_xboole_0 @ X10 @ X11))),
% 1.05/1.31      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.31  thf('76', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.31           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.05/1.31      inference('sup+', [status(thm)], ['74', '75'])).
% 1.05/1.31  thf('77', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('78', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('79', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.05/1.31           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.31      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.05/1.31  thf('80', plain,
% 1.05/1.31      ((((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.05/1.31          (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31          = (k2_xboole_0 @ sk_B @ 
% 1.05/1.31             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup+', [status(thm)], ['73', '79'])).
% 1.05/1.31  thf('81', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('82', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('sup+', [status(thm)], ['54', '56'])).
% 1.05/1.31  thf('83', plain,
% 1.05/1.31      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.31          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.05/1.31  thf('84', plain,
% 1.05/1.31      (((k1_tops_1 @ sk_A @ sk_B)
% 1.05/1.31         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.05/1.31  thf('85', plain,
% 1.05/1.31      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.05/1.31      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.31  thf('86', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.05/1.31      inference('sup+', [status(thm)], ['84', '85'])).
% 1.05/1.31  thf('87', plain,
% 1.05/1.31      (![X6 : $i, X7 : $i]:
% 1.05/1.31         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.31  thf('88', plain,
% 1.05/1.31      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.31         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('sup-', [status(thm)], ['86', '87'])).
% 1.05/1.31  thf('89', plain,
% 1.05/1.31      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.31  thf('90', plain,
% 1.05/1.31      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['88', '89'])).
% 1.05/1.31  thf('91', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.05/1.31  thf('92', plain,
% 1.05/1.31      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.31      inference('demod', [status(thm)], ['83', '90', '91'])).
% 1.05/1.31  thf('93', plain,
% 1.05/1.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('sat_resolution*', [status(thm)], ['32'])).
% 1.05/1.31  thf('94', plain,
% 1.05/1.31      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 1.05/1.31  thf('95', plain,
% 1.05/1.31      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 1.05/1.31  thf('96', plain,
% 1.05/1.31      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('sup+', [status(thm)], ['94', '95'])).
% 1.05/1.31  thf('97', plain,
% 1.05/1.31      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['72', '96'])).
% 1.05/1.31  thf('98', plain,
% 1.05/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf(t65_tops_1, axiom,
% 1.05/1.31    (![A:$i]:
% 1.05/1.31     ( ( l1_pre_topc @ A ) =>
% 1.05/1.31       ( ![B:$i]:
% 1.05/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.31           ( ( k2_pre_topc @ A @ B ) =
% 1.05/1.31             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.31  thf('99', plain,
% 1.05/1.31      (![X36 : $i, X37 : $i]:
% 1.05/1.31         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.05/1.31          | ((k2_pre_topc @ X37 @ X36)
% 1.05/1.31              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 1.05/1.31                 (k2_tops_1 @ X37 @ X36)))
% 1.05/1.31          | ~ (l1_pre_topc @ X37))),
% 1.05/1.31      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.05/1.31  thf('100', plain,
% 1.05/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.31        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.05/1.31            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.31      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.31  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.31  thf('102', plain,
% 1.05/1.31      (((k2_pre_topc @ sk_A @ sk_B)
% 1.05/1.31         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.31            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['100', '101'])).
% 1.05/1.31  thf('103', plain,
% 1.05/1.31      (((k2_pre_topc @ sk_A @ sk_B)
% 1.05/1.31         = (k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('sup+', [status(thm)], ['97', '102'])).
% 1.05/1.31  thf('104', plain,
% 1.05/1.31      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_pre_topc @ sk_A @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['63', '103'])).
% 1.05/1.31  thf('105', plain,
% 1.05/1.31      (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31         (k1_tops_1 @ sk_A @ sk_B)) = (k2_pre_topc @ sk_A @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['52', '53', '104'])).
% 1.05/1.31  thf('106', plain,
% 1.05/1.31      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.31         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.31  thf('107', plain,
% 1.05/1.31      (![X12 : $i, X13 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.05/1.31           = (k3_xboole_0 @ X12 @ X13))),
% 1.05/1.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.31  thf('108', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['43', '44'])).
% 1.05/1.31  thf('109', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.05/1.31      inference('sup+', [status(thm)], ['107', '108'])).
% 1.05/1.31  thf(t25_subset_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.31       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.05/1.31         ( k2_subset_1 @ A ) ) ))).
% 1.05/1.31  thf('110', plain,
% 1.05/1.31      (![X25 : $i, X26 : $i]:
% 1.05/1.31         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26))
% 1.05/1.31            = (k2_subset_1 @ X25))
% 1.05/1.31          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.05/1.31      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.05/1.31  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.05/1.31  thf('111', plain, (![X14 : $i]: ((k2_subset_1 @ X14) = (X14))),
% 1.05/1.31      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.05/1.31  thf('112', plain,
% 1.05/1.31      (![X25 : $i, X26 : $i]:
% 1.05/1.31         (((k4_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X26)) = (X25))
% 1.05/1.31          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.05/1.31      inference('demod', [status(thm)], ['110', '111'])).
% 1.05/1.31  thf('113', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k4_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 1.05/1.31           (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))) = (X0))),
% 1.05/1.31      inference('sup-', [status(thm)], ['109', '112'])).
% 1.05/1.31  thf('114', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.05/1.31      inference('sup+', [status(thm)], ['107', '108'])).
% 1.05/1.31  thf(d5_subset_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.05/1.31  thf('115', plain,
% 1.05/1.31      (![X15 : $i, X16 : $i]:
% 1.05/1.31         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 1.05/1.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 1.05/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.05/1.31  thf('116', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.05/1.31           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.31      inference('sup-', [status(thm)], ['114', '115'])).
% 1.05/1.31  thf('117', plain,
% 1.05/1.31      (![X12 : $i, X13 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.05/1.31           = (k3_xboole_0 @ X12 @ X13))),
% 1.05/1.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.31  thf('118', plain,
% 1.05/1.31      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.05/1.31      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.31  thf('119', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.05/1.31      inference('sup+', [status(thm)], ['117', '118'])).
% 1.05/1.31  thf('120', plain,
% 1.05/1.31      (![X6 : $i, X7 : $i]:
% 1.05/1.31         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.31  thf('121', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.05/1.31           = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('sup-', [status(thm)], ['119', '120'])).
% 1.05/1.31  thf('122', plain,
% 1.05/1.31      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.05/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.31  thf('123', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.05/1.31           = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.31      inference('demod', [status(thm)], ['121', '122'])).
% 1.05/1.31  thf(t100_xboole_1, axiom,
% 1.05/1.31    (![A:$i,B:$i]:
% 1.05/1.31     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.31  thf('124', plain,
% 1.05/1.31      (![X4 : $i, X5 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X4 @ X5)
% 1.05/1.31           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.05/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.31  thf('125', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.31           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.31      inference('sup+', [status(thm)], ['123', '124'])).
% 1.05/1.31  thf('126', plain,
% 1.05/1.31      (![X4 : $i, X5 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X4 @ X5)
% 1.05/1.31           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.05/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.31  thf('127', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.31           = (k4_xboole_0 @ X1 @ X0))),
% 1.05/1.31      inference('demod', [status(thm)], ['125', '126'])).
% 1.05/1.31  thf('128', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.31           = (k4_xboole_0 @ X1 @ X0))),
% 1.05/1.31      inference('sup+', [status(thm)], ['116', '127'])).
% 1.05/1.31  thf('129', plain,
% 1.05/1.31      (![X0 : $i, X1 : $i]:
% 1.05/1.31         ((k4_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 1.05/1.31           = (X0))),
% 1.05/1.31      inference('demod', [status(thm)], ['113', '128'])).
% 1.05/1.31  thf('130', plain,
% 1.05/1.31      (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31         (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.05/1.31      inference('sup+', [status(thm)], ['106', '129'])).
% 1.05/1.31  thf('131', plain,
% 1.05/1.31      (((k1_tops_1 @ sk_A @ sk_B)
% 1.05/1.31         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.05/1.31  thf('132', plain,
% 1.05/1.31      (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.31         (k1_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.05/1.31      inference('demod', [status(thm)], ['130', '131'])).
% 1.05/1.31  thf('133', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.05/1.31      inference('sup+', [status(thm)], ['105', '132'])).
% 1.05/1.31  thf('134', plain, (((v4_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.05/1.31      inference('demod', [status(thm)], ['41', '133'])).
% 1.05/1.31  thf('135', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 1.05/1.31      inference('simplify', [status(thm)], ['134'])).
% 1.05/1.31  thf('136', plain, ($false), inference('demod', [status(thm)], ['35', '135'])).
% 1.05/1.31  
% 1.05/1.31  % SZS output end Refutation
% 1.05/1.31  
% 1.05/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
