%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o1S5gWCy6n

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 367 expanded)
%              Number of leaves         :   34 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          : 1286 (4762 expanded)
%              Number of equality atoms :   83 ( 235 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
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

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('54',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
        = ( k2_subset_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('56',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_subset_1 @ X17 @ X18 @ ( k3_subset_1 @ X17 @ X18 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('60',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('64',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('76',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','80'])).

thf('82',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('83',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('85',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('86',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','89'])).

thf('91',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o1S5gWCy6n
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 659 iterations in 0.230s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.48/0.68  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.48/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.48/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.68  thf(t77_tops_1, conjecture,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.68             ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.68               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i]:
% 0.48/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68          ( ![B:$i]:
% 0.48/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68              ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.68                ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.68                  ( k7_subset_1 @
% 0.48/0.68                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68              (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (~
% 0.48/0.68       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.68        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t52_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.48/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.48/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X24 : $i, X25 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.48/0.68          | ~ (v4_pre_topc @ X24 @ X25)
% 0.48/0.68          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.48/0.68          | ~ (l1_pre_topc @ X25))),
% 0.48/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.48/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['3', '8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(l78_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.68             ( k7_subset_1 @
% 0.48/0.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.48/0.68               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X30 : $i, X31 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.48/0.68          | ((k2_tops_1 @ X31 @ X30)
% 0.48/0.68              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.48/0.68                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.48/0.68          | ~ (l1_pre_topc @ X31))),
% 0.48/0.68      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.68               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.48/0.68            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['9', '14'])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.48/0.68          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['15', '18'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68              (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= (~
% 0.48/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= (~
% 0.48/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.48/0.68         <= (~
% 0.48/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.48/0.68             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['19', '22'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.68       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t44_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X32 : $i, X33 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.48/0.68          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.48/0.68          | ~ (l1_pre_topc @ X33))),
% 0.48/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('33', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.48/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X21 : $i, X23 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf(dt_k3_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X9 : $i, X10 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.48/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.48/0.68        (k1_zfmisc_1 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X21 : $i, X22 : $i]:
% 0.48/0.68         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      ((r1_tarski @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.48/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf(d5_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.48/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '42'])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['28', '43'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X21 : $i, X23 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf(redefinition_k4_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.48/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.48/0.68          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.48/0.68            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.48/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68          (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.68          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68             (k2_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['46', '49'])).
% 0.48/0.68  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.68  thf('51', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.68  thf('52', plain,
% 0.48/0.68      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68          (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.68          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.48/0.68  thf('53', plain,
% 0.48/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('54', plain,
% 0.48/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf(t25_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.48/0.68         ( k2_subset_1 @ A ) ) ))).
% 0.48/0.68  thf('55', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         (((k4_subset_1 @ X17 @ X18 @ (k3_subset_1 @ X17 @ X18))
% 0.48/0.68            = (k2_subset_1 @ X17))
% 0.48/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.48/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.68  thf('56', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('57', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         (((k4_subset_1 @ X17 @ X18 @ (k3_subset_1 @ X17 @ X18)) = (X17))
% 0.48/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.48/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.48/0.68  thf('58', plain,
% 0.48/0.68      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['54', '57'])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf('60', plain,
% 0.48/0.68      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68         (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.48/0.68  thf('61', plain,
% 0.48/0.68      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['53', '60'])).
% 0.48/0.68  thf('62', plain,
% 0.48/0.68      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.68          = (sk_B)))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['52', '61'])).
% 0.48/0.68  thf(t6_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.68  thf('63', plain,
% 0.48/0.68      (![X4 : $i, X5 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5))
% 0.48/0.68           = (k2_xboole_0 @ X4 @ X5))),
% 0.48/0.68      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.48/0.68  thf('64', plain,
% 0.48/0.68      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.48/0.68          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.48/0.68  thf('65', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.68  thf('66', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(dt_k2_tops_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.48/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.68       ( m1_subset_1 @
% 0.48/0.68         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.48/0.68  thf('67', plain,
% 0.48/0.68      (![X26 : $i, X27 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X26)
% 0.48/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.48/0.68          | (m1_subset_1 @ (k2_tops_1 @ X26 @ X27) @ 
% 0.48/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.48/0.68  thf('68', plain,
% 0.48/0.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.48/0.68  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('70', plain,
% 0.48/0.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['68', '69'])).
% 0.48/0.68  thf('71', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('72', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.48/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.48/0.68          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.68  thf('73', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.68            = (k2_xboole_0 @ sk_B @ X0))
% 0.48/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.48/0.68  thf('74', plain,
% 0.48/0.68      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['70', '73'])).
% 0.48/0.68  thf('75', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t65_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( k2_pre_topc @ A @ B ) =
% 0.48/0.68             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.68  thf('76', plain,
% 0.48/0.68      (![X34 : $i, X35 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.48/0.68          | ((k2_pre_topc @ X35 @ X34)
% 0.48/0.68              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.48/0.68                 (k2_tops_1 @ X35 @ X34)))
% 0.48/0.68          | ~ (l1_pre_topc @ X35))),
% 0.48/0.68      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.48/0.68  thf('77', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.68            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['75', '76'])).
% 0.48/0.68  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('79', plain,
% 0.48/0.68      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.68         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.48/0.68  thf('80', plain,
% 0.48/0.68      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.68         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['74', '79'])).
% 0.48/0.68  thf('81', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.68          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('demod', [status(thm)], ['64', '65', '80'])).
% 0.48/0.68  thf('82', plain,
% 0.48/0.68      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.68          = (sk_B)))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['52', '61'])).
% 0.48/0.68  thf('83', plain,
% 0.48/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['81', '82'])).
% 0.48/0.68  thf('84', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(fc1_tops_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.48/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.68       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.48/0.68  thf('85', plain,
% 0.48/0.68      (![X28 : $i, X29 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X28)
% 0.48/0.68          | ~ (v2_pre_topc @ X28)
% 0.48/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.48/0.68          | (v4_pre_topc @ (k2_pre_topc @ X28 @ X29) @ X28))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.48/0.68  thf('86', plain,
% 0.48/0.68      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.48/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.48/0.68  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('89', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.48/0.68      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.48/0.68  thf('90', plain,
% 0.48/0.68      (((v4_pre_topc @ sk_B @ sk_A))
% 0.48/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['83', '89'])).
% 0.48/0.68  thf('91', plain,
% 0.48/0.68      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('92', plain,
% 0.48/0.68      (~
% 0.48/0.68       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.68       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['90', '91'])).
% 0.48/0.68  thf('93', plain, ($false),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '92'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
