%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpFcyA1igq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 239 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  934 (2734 expanded)
%              Number of equality atoms :   62 ( 145 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
       != X30 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['16','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['74','75'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['56','57','58','79','80'])).

thf('82',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['41','81'])).

thf('83',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['35','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpFcyA1igq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 1065 iterations in 0.397s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.60/0.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.60/0.85  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.60/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.60/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.85  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.60/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.85  thf(t77_tops_1, conjecture,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( v4_pre_topc @ B @ A ) <=>
% 0.60/0.85             ( ( k2_tops_1 @ A @ B ) =
% 0.60/0.85               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i]:
% 0.60/0.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85          ( ![B:$i]:
% 0.60/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85              ( ( v4_pre_topc @ B @ A ) <=>
% 0.60/0.85                ( ( k2_tops_1 @ A @ B ) =
% 0.60/0.85                  ( k7_subset_1 @
% 0.60/0.85                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.60/0.85  thf('0', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85              (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('1', plain,
% 0.60/0.85      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('2', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t74_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( k1_tops_1 @ A @ B ) =
% 0.60/0.85             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.85  thf('3', plain,
% 0.60/0.85      (![X36 : $i, X37 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.60/0.85          | ((k1_tops_1 @ X37 @ X36)
% 0.60/0.85              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.60/0.85                 (k2_tops_1 @ X37 @ X36)))
% 0.60/0.85          | ~ (l1_pre_topc @ X37))),
% 0.60/0.85      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.85        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.85            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.85  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('6', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(redefinition_k7_subset_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.60/0.85  thf('7', plain,
% 0.60/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.60/0.85          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.60/0.85  thf('8', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.85           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.85  thf('9', plain,
% 0.60/0.85      (((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.85         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.60/0.85  thf(t48_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.85  thf('10', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.85           = (k3_xboole_0 @ X15 @ X16))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('11', plain,
% 0.60/0.85      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['9', '10'])).
% 0.60/0.85  thf('12', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85             (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('13', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.85           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.85  thf('14', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13'])).
% 0.60/0.85  thf(t36_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.60/0.85  thf('15', plain,
% 0.60/0.85      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.60/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.85  thf('16', plain,
% 0.60/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.60/0.85        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t69_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( v4_pre_topc @ B @ A ) =>
% 0.60/0.85             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.60/0.85  thf('18', plain,
% 0.60/0.85      (![X34 : $i, X35 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.60/0.85          | (r1_tarski @ (k2_tops_1 @ X35 @ X34) @ X34)
% 0.60/0.85          | ~ (v4_pre_topc @ X34 @ X35)
% 0.60/0.85          | ~ (l1_pre_topc @ X35))),
% 0.60/0.85      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.60/0.85  thf('19', plain,
% 0.60/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.85        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.60/0.85        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.85  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('21', plain,
% 0.60/0.85      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.60/0.85        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('22', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.60/0.85      inference('clc', [status(thm)], ['16', '21'])).
% 0.60/0.85  thf(t28_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      (![X11 : $i, X12 : $i]:
% 0.60/0.85         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.60/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.85  thf('24', plain,
% 0.60/0.85      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.60/0.85         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.85  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.85  thf('25', plain,
% 0.60/0.85      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.85  thf('27', plain,
% 0.60/0.85      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.60/0.85      inference('sup+', [status(thm)], ['11', '26'])).
% 0.60/0.85  thf('28', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.85           = (k4_xboole_0 @ sk_B @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.85  thf('29', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85              (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= (~
% 0.60/0.85             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('30', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.60/0.85         <= (~
% 0.60/0.85             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.85  thf('31', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.60/0.85         <= (~
% 0.60/0.85             (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['27', '30'])).
% 0.60/0.85  thf('32', plain,
% 0.60/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['31'])).
% 0.60/0.85  thf('33', plain,
% 0.60/0.85      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.60/0.85       ~
% 0.60/0.85       (((k2_tops_1 @ sk_A @ sk_B)
% 0.60/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('34', plain, (~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.60/0.85      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.60/0.85  thf('35', plain, (~ (v4_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.60/0.85  thf('36', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t52_pre_topc, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.60/0.85             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.60/0.85               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.60/0.85  thf('37', plain,
% 0.60/0.85      (![X30 : $i, X31 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.60/0.85          | ~ (v2_pre_topc @ X31)
% 0.60/0.85          | ((k2_pre_topc @ X31 @ X30) != (X30))
% 0.60/0.85          | (v4_pre_topc @ X30 @ X31)
% 0.60/0.85          | ~ (l1_pre_topc @ X31))),
% 0.60/0.85      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.60/0.85  thf('38', plain,
% 0.60/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.85        | (v4_pre_topc @ sk_B @ sk_A)
% 0.60/0.85        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.60/0.85        | ~ (v2_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.85  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('41', plain,
% 0.60/0.85      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.60/0.85  thf('42', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t3_subset, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.85  thf('43', plain,
% 0.60/0.85      (![X27 : $i, X28 : $i]:
% 0.60/0.85         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('44', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      (![X11 : $i, X12 : $i]:
% 0.60/0.85         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.60/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.85  thf('46', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.85           = (k3_xboole_0 @ X15 @ X16))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('49', plain,
% 0.60/0.85      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.60/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.85  thf('50', plain,
% 0.60/0.85      (![X27 : $i, X29 : $i]:
% 0.60/0.85         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('51', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['49', '50'])).
% 0.60/0.85  thf('52', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.60/0.85      inference('sup+', [status(thm)], ['48', '51'])).
% 0.60/0.85  thf('53', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup+', [status(thm)], ['47', '52'])).
% 0.60/0.85  thf(t65_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( k2_pre_topc @ A @ B ) =
% 0.60/0.85             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.85  thf('54', plain,
% 0.60/0.85      (![X32 : $i, X33 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.60/0.85          | ((k2_pre_topc @ X33 @ X32)
% 0.60/0.85              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.60/0.85                 (k2_tops_1 @ X33 @ X32)))
% 0.60/0.85          | ~ (l1_pre_topc @ X33))),
% 0.60/0.85      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.60/0.85  thf('55', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X0)
% 0.60/0.85          | ((k2_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 0.60/0.85              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.60/0.85                 (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 0.60/0.85                 (k2_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.60/0.85          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.60/0.85             (k2_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup+', [status(thm)], ['46', '55'])).
% 0.60/0.85  thf('57', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.85  thf('58', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.85  thf('59', plain,
% 0.60/0.85      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.85  thf('60', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('61', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i]:
% 0.60/0.85         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.60/0.85           = (k3_xboole_0 @ X15 @ X16))),
% 0.60/0.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.60/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.60/0.85      inference('sup+', [status(thm)], ['61', '62'])).
% 0.60/0.85  thf(t1_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.85       ( r1_tarski @ A @ C ) ))).
% 0.60/0.85  thf('64', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.85         (~ (r1_tarski @ X8 @ X9)
% 0.60/0.85          | ~ (r1_tarski @ X9 @ X10)
% 0.60/0.85          | (r1_tarski @ X8 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.85  thf('65', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.85      inference('sup-', [status(thm)], ['63', '64'])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['60', '65'])).
% 0.60/0.85  thf('67', plain,
% 0.60/0.85      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup+', [status(thm)], ['59', '66'])).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      (![X27 : $i, X29 : $i]:
% 0.60/0.85         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.85  thf('70', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(redefinition_k4_subset_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.60/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.60/0.85       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.60/0.85  thf('71', plain,
% 0.60/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.60/0.85          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.60/0.85  thf('72', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.60/0.85            = (k2_xboole_0 @ sk_B @ X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.60/0.85  thf('73', plain,
% 0.60/0.85      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['69', '72'])).
% 0.60/0.85  thf('74', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.60/0.85      inference('clc', [status(thm)], ['16', '21'])).
% 0.60/0.85  thf(t12_xboole_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.60/0.85  thf('75', plain,
% 0.60/0.85      (![X6 : $i, X7 : $i]:
% 0.60/0.85         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.60/0.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.85  thf('76', plain,
% 0.60/0.85      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['74', '75'])).
% 0.60/0.85  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.85  thf('78', plain,
% 0.60/0.85      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['76', '77'])).
% 0.60/0.85  thf('79', plain,
% 0.60/0.85      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.60/0.85         = (sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['73', '78'])).
% 0.60/0.85  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('81', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['56', '57', '58', '79', '80'])).
% 0.60/0.85  thf('82', plain, (((v4_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['41', '81'])).
% 0.60/0.85  thf('83', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('simplify', [status(thm)], ['82'])).
% 0.60/0.85  thf('84', plain, ($false), inference('demod', [status(thm)], ['35', '83'])).
% 0.60/0.85  
% 0.60/0.85  % SZS output end Refutation
% 0.60/0.85  
% 0.60/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
