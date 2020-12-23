%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WCFj2kJ7R2

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 258 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          : 1016 (3517 expanded)
%              Number of equality atoms :   72 ( 207 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X36 @ X35 ) @ X35 )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
       != X31 )
      | ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['11','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k1_tops_1 @ X38 @ X37 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['13','56'])).

thf('73',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WCFj2kJ7R2
% 0.17/0.35  % Computer   : n008.cluster.edu
% 0.17/0.35  % Model      : x86_64 x86_64
% 0.17/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.35  % Memory     : 8042.1875MB
% 0.17/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.35  % CPULimit   : 60
% 0.17/0.35  % DateTime   : Tue Dec  1 14:46:45 EST 2020
% 0.17/0.35  % CPUTime    : 
% 0.17/0.35  % Running portfolio for 600 s
% 0.17/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.35  % Number of cores: 8
% 0.17/0.36  % Python version: Python 3.6.8
% 0.17/0.36  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 921 iterations in 0.285s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.47/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.47/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.47/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.71  thf(t77_tops_1, conjecture,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.47/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.47/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i]:
% 0.47/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.71          ( ![B:$i]:
% 0.47/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.47/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.47/0.71                  ( k7_subset_1 @
% 0.47/0.71                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.47/0.71  thf('0', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B)))
% 0.47/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('1', plain,
% 0.47/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.71      inference('split', [status(esa)], ['0'])).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t69_tops_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_pre_topc @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( v4_pre_topc @ B @ A ) =>
% 0.47/0.71             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (![X35 : $i, X36 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.47/0.71          | (r1_tarski @ (k2_tops_1 @ X36 @ X35) @ X35)
% 0.47/0.71          | ~ (v4_pre_topc @ X35 @ X36)
% 0.47/0.71          | ~ (l1_pre_topc @ X36))),
% 0.47/0.71      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.47/0.71  thf('4', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.47/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.47/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.71  thf('7', plain,
% 0.47/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.47/0.71  thf(t28_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.71  thf('8', plain,
% 0.47/0.71      (![X14 : $i, X15 : $i]:
% 0.47/0.71         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.47/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.71  thf('9', plain,
% 0.47/0.71      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.47/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.47/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.47/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.47/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71              (k1_tops_1 @ sk_A @ sk_B)))
% 0.47/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('13', plain,
% 0.47/0.71      (~
% 0.47/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.47/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.47/0.71      inference('split', [status(esa)], ['12'])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t65_tops_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_pre_topc @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( k2_pre_topc @ A @ B ) =
% 0.47/0.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.71  thf('15', plain,
% 0.47/0.71      (![X33 : $i, X34 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.47/0.71          | ((k2_pre_topc @ X34 @ X33)
% 0.47/0.71              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.47/0.71                 (k2_tops_1 @ X34 @ X33)))
% 0.47/0.71          | ~ (l1_pre_topc @ X34))),
% 0.47/0.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.71        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.47/0.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.71  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.47/0.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.47/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.71  thf('19', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t3_subset, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      (![X28 : $i, X29 : $i]:
% 0.47/0.71         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('21', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.71  thf('22', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.47/0.71          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.47/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('25', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('split', [status(esa)], ['0'])).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf(t36_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.47/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.71  thf('28', plain,
% 0.47/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.71  thf(t1_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.71       ( r1_tarski @ A @ C ) ))).
% 0.47/0.71  thf('29', plain,
% 0.47/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.71         (~ (r1_tarski @ X11 @ X12)
% 0.47/0.71          | ~ (r1_tarski @ X12 @ X13)
% 0.47/0.71          | (r1_tarski @ X11 @ X13))),
% 0.47/0.71      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.71  thf('30', plain,
% 0.47/0.71      ((![X0 : $i]:
% 0.47/0.71          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.47/0.71           | ~ (r1_tarski @ sk_B @ X0)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.71  thf('31', plain,
% 0.47/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['21', '30'])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      (![X28 : $i, X30 : $i]:
% 0.47/0.71         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.47/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.47/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.71  thf('34', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.47/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.47/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.47/0.71          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.47/0.71            = (k2_xboole_0 @ sk_B @ X0))
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.71  thf('37', plain,
% 0.47/0.71      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.47/0.71          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['33', '36'])).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.47/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.71  thf(t12_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      (![X9 : $i, X10 : $i]:
% 0.47/0.71         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.71  thf('42', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.71  thf('43', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.71  thf('44', plain,
% 0.47/0.71      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['38', '43'])).
% 0.47/0.71  thf('45', plain,
% 0.47/0.71      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.47/0.71          = (sk_B)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('demod', [status(thm)], ['37', '44'])).
% 0.47/0.71  thf('46', plain,
% 0.47/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup+', [status(thm)], ['18', '45'])).
% 0.47/0.71  thf('47', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t52_pre_topc, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_pre_topc @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.47/0.71             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.47/0.71               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.47/0.71  thf('48', plain,
% 0.47/0.71      (![X31 : $i, X32 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.47/0.71          | ~ (v2_pre_topc @ X32)
% 0.47/0.71          | ((k2_pre_topc @ X32 @ X31) != (X31))
% 0.47/0.71          | (v4_pre_topc @ X31 @ X32)
% 0.47/0.71          | ~ (l1_pre_topc @ X32))),
% 0.47/0.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.47/0.71  thf('49', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.71        | (v4_pre_topc @ sk_B @ sk_A)
% 0.47/0.71        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.47/0.71        | ~ (v2_pre_topc @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.71  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('52', plain,
% 0.47/0.71      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.47/0.71  thf('53', plain,
% 0.47/0.71      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['46', '52'])).
% 0.47/0.71  thf('54', plain,
% 0.47/0.71      (((v4_pre_topc @ sk_B @ sk_A))
% 0.47/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.71  thf('55', plain,
% 0.47/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.71      inference('split', [status(esa)], ['12'])).
% 0.47/0.71  thf('56', plain,
% 0.47/0.71      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.47/0.71       ~
% 0.47/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.71  thf('57', plain,
% 0.47/0.71      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.47/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.47/0.71      inference('split', [status(esa)], ['0'])).
% 0.47/0.71  thf('58', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.47/0.71      inference('sat_resolution*', [status(thm)], ['13', '56', '57'])).
% 0.47/0.71  thf('59', plain,
% 0.47/0.71      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.47/0.71         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.47/0.71      inference('simpl_trail', [status(thm)], ['11', '58'])).
% 0.47/0.71  thf('60', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t74_tops_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_pre_topc @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.71           ( ( k1_tops_1 @ A @ B ) =
% 0.47/0.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.71  thf('61', plain,
% 0.47/0.71      (![X37 : $i, X38 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.47/0.71          | ((k1_tops_1 @ X38 @ X37)
% 0.47/0.71              = (k7_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 0.47/0.71                 (k2_tops_1 @ X38 @ X37)))
% 0.47/0.71          | ~ (l1_pre_topc @ X38))),
% 0.47/0.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.47/0.71  thf('62', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.71        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.47/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.71  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('64', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.47/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('65', plain,
% 0.47/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.47/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.47/0.71      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.47/0.71  thf(t48_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.71  thf('66', plain,
% 0.47/0.71      (![X18 : $i, X19 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.47/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.47/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.71  thf('67', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.47/0.71         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['65', '66'])).
% 0.47/0.71  thf('68', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.47/0.71         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['59', '67'])).
% 0.47/0.71  thf('69', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71              (k1_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= (~
% 0.47/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('split', [status(esa)], ['12'])).
% 0.47/0.71  thf('70', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.47/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('71', plain,
% 0.47/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.47/0.71         <= (~
% 0.47/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.47/0.71      inference('demod', [status(thm)], ['69', '70'])).
% 0.47/0.71  thf('72', plain,
% 0.47/0.71      (~
% 0.47/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.47/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.47/0.71      inference('sat_resolution*', [status(thm)], ['13', '56'])).
% 0.47/0.71  thf('73', plain,
% 0.47/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.47/0.71         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.47/0.71      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 0.47/0.71  thf('74', plain, ($false),
% 0.47/0.71      inference('simplify_reflect-', [status(thm)], ['68', '73'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.57/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
