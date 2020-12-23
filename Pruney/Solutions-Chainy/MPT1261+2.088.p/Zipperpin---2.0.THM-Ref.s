%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pjc5bQwMD5

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 183 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          : 1060 (2161 expanded)
%              Number of equality atoms :   83 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k2_pre_topc @ X41 @ X40 ) @ ( k1_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 @ ( k2_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('78',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X38 @ X39 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('79',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pjc5bQwMD5
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:13:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 594 iterations in 0.238s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.70  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.48/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.48/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.70  thf(t77_tops_1, conjecture,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.70             ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.70               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i]:
% 0.48/0.70        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.70          ( ![B:$i]:
% 0.48/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70              ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.70                ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.70                  ( k7_subset_1 @
% 0.48/0.70                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.48/0.70  thf('0', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70              (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      (~
% 0.48/0.70       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.70       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.70        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t52_pre_topc, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( l1_pre_topc @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.48/0.70             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.48/0.70               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X34 : $i, X35 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.48/0.70          | ~ (v4_pre_topc @ X34 @ X35)
% 0.48/0.70          | ((k2_pre_topc @ X35 @ X34) = (X34))
% 0.48/0.70          | ~ (l1_pre_topc @ X35))),
% 0.48/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.70  thf('6', plain,
% 0.48/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.48/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.70  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('demod', [status(thm)], ['6', '7'])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.70         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['3', '8'])).
% 0.48/0.70  thf('10', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(l78_tops_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( l1_pre_topc @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.70             ( k7_subset_1 @
% 0.48/0.70               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.48/0.70               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.70  thf('11', plain,
% 0.48/0.70      (![X40 : $i, X41 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.48/0.70          | ((k2_tops_1 @ X41 @ X40)
% 0.48/0.70              = (k7_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.48/0.70                 (k2_pre_topc @ X41 @ X40) @ (k1_tops_1 @ X41 @ X40)))
% 0.48/0.70          | ~ (l1_pre_topc @ X41))),
% 0.48/0.70      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.70               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.70  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.48/0.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['9', '14'])).
% 0.48/0.70  thf('16', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k7_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.48/0.70          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['15', '18'])).
% 0.48/0.70  thf('20', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70              (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= (~
% 0.48/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= (~
% 0.48/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.48/0.70         <= (~
% 0.48/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.48/0.70             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['19', '22'])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.70       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.70       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf('26', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.70  thf(t41_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.48/0.70           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.48/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.70  thf(t1_boole, axiom,
% 0.48/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.70  thf('31', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.48/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.70  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['30', '31'])).
% 0.48/0.70  thf(t39_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X10 : $i, X11 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.48/0.70           = (k2_xboole_0 @ X10 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['32', '33'])).
% 0.48/0.70  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['30', '31'])).
% 0.48/0.70  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.48/0.70  thf(t48_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      (![X15 : $i, X16 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.48/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.48/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['36', '37'])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X15 : $i, X16 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.48/0.70           = (k3_xboole_0 @ X15 @ X16))),
% 0.48/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.70  thf(t36_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.48/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.70  thf(t4_subset_1, axiom,
% 0.48/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.70  thf('41', plain,
% 0.48/0.70      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.70  thf(t3_subset, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X28 : $i, X29 : $i]:
% 0.48/0.70         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.70  thf(d10_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      (![X4 : $i, X6 : $i]:
% 0.48/0.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['40', '45'])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['39', '46'])).
% 0.48/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['47', '48'])).
% 0.48/0.70  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['38', '49'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.48/0.70           = (k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['29', '50'])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X10 : $i, X11 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.48/0.70           = (k2_xboole_0 @ X10 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['51', '52'])).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.48/0.70           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X10 : $i, X11 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.48/0.70           = (k2_xboole_0 @ X10 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.48/0.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['54', '55'])).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.48/0.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['53', '56'])).
% 0.48/0.70  thf('58', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.48/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.70  thf('59', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.48/0.70  thf('60', plain,
% 0.48/0.70      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.48/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['28', '59'])).
% 0.48/0.70  thf('61', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(dt_k2_tops_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.48/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.70       ( m1_subset_1 @
% 0.48/0.70         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      (![X36 : $i, X37 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X36)
% 0.48/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.48/0.70          | (m1_subset_1 @ (k2_tops_1 @ X36 @ X37) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X36))))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.48/0.70  thf('63', plain,
% 0.48/0.70      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.70  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['63', '64'])).
% 0.48/0.70  thf('66', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k4_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.48/0.70  thf('67', plain,
% 0.48/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.48/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.48/0.70          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.70  thf('68', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.70            = (k2_xboole_0 @ sk_B @ X0))
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['66', '67'])).
% 0.48/0.70  thf('69', plain,
% 0.48/0.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.70         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['65', '68'])).
% 0.48/0.70  thf('70', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t65_tops_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( l1_pre_topc @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( k2_pre_topc @ A @ B ) =
% 0.48/0.70             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.70  thf('71', plain,
% 0.48/0.70      (![X42 : $i, X43 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.48/0.70          | ((k2_pre_topc @ X43 @ X42)
% 0.48/0.70              = (k4_subset_1 @ (u1_struct_0 @ X43) @ X42 @ 
% 0.48/0.70                 (k2_tops_1 @ X43 @ X42)))
% 0.48/0.70          | ~ (l1_pre_topc @ X43))),
% 0.48/0.70      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.48/0.70  thf('72', plain,
% 0.48/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.70            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.70  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('74', plain,
% 0.48/0.70      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.70         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.70  thf('75', plain,
% 0.48/0.70      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.70         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['69', '74'])).
% 0.48/0.70  thf('76', plain,
% 0.48/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['60', '75'])).
% 0.48/0.70  thf('77', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(fc1_tops_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.48/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.70       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (![X38 : $i, X39 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X38)
% 0.48/0.70          | ~ (v2_pre_topc @ X38)
% 0.48/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.48/0.70          | (v4_pre_topc @ (k2_pre_topc @ X38 @ X39) @ X38))),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.48/0.70  thf('79', plain,
% 0.48/0.70      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.48/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['77', '78'])).
% 0.48/0.70  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('82', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.48/0.70      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.48/0.70  thf('83', plain,
% 0.48/0.70      (((v4_pre_topc @ sk_B @ sk_A))
% 0.48/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['76', '82'])).
% 0.48/0.70  thf('84', plain,
% 0.48/0.70      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('85', plain,
% 0.48/0.70      (~
% 0.48/0.70       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.70             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.70       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['83', '84'])).
% 0.48/0.70  thf('86', plain, ($false),
% 0.48/0.70      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '85'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
