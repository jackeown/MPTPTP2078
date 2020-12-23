%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KuCq7xspaF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:42 EST 2020

% Result     : Theorem 5.74s
% Output     : Refutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 862 expanded)
%              Number of leaves         :   38 ( 273 expanded)
%              Depth                    :   18
%              Number of atoms          : 1589 (10169 expanded)
%              Number of equality atoms :  119 ( 646 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_pre_topc @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X37 @ X36 ) @ X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('55',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('61',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('88',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('97',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( k2_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','86','107'])).

thf('109',plain,
    ( ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','86','107'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('112',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('114',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('115',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['112','118'])).

thf('120',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KuCq7xspaF
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.74/5.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.74/5.94  % Solved by: fo/fo7.sh
% 5.74/5.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.74/5.94  % done 1938 iterations in 5.478s
% 5.74/5.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.74/5.94  % SZS output start Refutation
% 5.74/5.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.74/5.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.74/5.94  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.74/5.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.74/5.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.74/5.94  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.74/5.94  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.74/5.94  thf(sk_A_type, type, sk_A: $i).
% 5.74/5.94  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.74/5.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.74/5.94  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.74/5.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.74/5.94  thf(sk_B_type, type, sk_B: $i).
% 5.74/5.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.74/5.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.74/5.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.74/5.94  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.74/5.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.74/5.94  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.74/5.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.74/5.94  thf(t77_tops_1, conjecture,
% 5.74/5.94    (![A:$i]:
% 5.74/5.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.74/5.94       ( ![B:$i]:
% 5.74/5.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94           ( ( v4_pre_topc @ B @ A ) <=>
% 5.74/5.94             ( ( k2_tops_1 @ A @ B ) =
% 5.74/5.94               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.74/5.94  thf(zf_stmt_0, negated_conjecture,
% 5.74/5.94    (~( ![A:$i]:
% 5.74/5.94        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.74/5.94          ( ![B:$i]:
% 5.74/5.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94              ( ( v4_pre_topc @ B @ A ) <=>
% 5.74/5.94                ( ( k2_tops_1 @ A @ B ) =
% 5.74/5.94                  ( k7_subset_1 @
% 5.74/5.94                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 5.74/5.94    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 5.74/5.94  thf('0', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94              (k1_tops_1 @ sk_A @ sk_B)))
% 5.74/5.94        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('1', plain,
% 5.74/5.94      (~
% 5.74/5.94       (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.74/5.94       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('split', [status(esa)], ['0'])).
% 5.74/5.94  thf('2', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B)))
% 5.74/5.94        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('3', plain,
% 5.74/5.94      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('split', [status(esa)], ['2'])).
% 5.74/5.94  thf('4', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(t52_pre_topc, axiom,
% 5.74/5.94    (![A:$i]:
% 5.74/5.94     ( ( l1_pre_topc @ A ) =>
% 5.74/5.94       ( ![B:$i]:
% 5.74/5.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.74/5.94             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.74/5.94               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.74/5.94  thf('5', plain,
% 5.74/5.94      (![X28 : $i, X29 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.74/5.94          | ~ (v4_pre_topc @ X28 @ X29)
% 5.74/5.94          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 5.74/5.94          | ~ (l1_pre_topc @ X29))),
% 5.74/5.94      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.74/5.94  thf('6', plain,
% 5.74/5.94      ((~ (l1_pre_topc @ sk_A)
% 5.74/5.94        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 5.74/5.94        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('sup-', [status(thm)], ['4', '5'])).
% 5.74/5.94  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('8', plain,
% 5.74/5.94      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('demod', [status(thm)], ['6', '7'])).
% 5.74/5.94  thf('9', plain,
% 5.74/5.94      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 5.74/5.94         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['3', '8'])).
% 5.74/5.94  thf('10', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(l78_tops_1, axiom,
% 5.74/5.94    (![A:$i]:
% 5.74/5.94     ( ( l1_pre_topc @ A ) =>
% 5.74/5.94       ( ![B:$i]:
% 5.74/5.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94           ( ( k2_tops_1 @ A @ B ) =
% 5.74/5.94             ( k7_subset_1 @
% 5.74/5.94               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.74/5.94               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.74/5.94  thf('11', plain,
% 5.74/5.94      (![X34 : $i, X35 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.74/5.94          | ((k2_tops_1 @ X35 @ X34)
% 5.74/5.94              = (k7_subset_1 @ (u1_struct_0 @ X35) @ 
% 5.74/5.94                 (k2_pre_topc @ X35 @ X34) @ (k1_tops_1 @ X35 @ X34)))
% 5.74/5.94          | ~ (l1_pre_topc @ X35))),
% 5.74/5.94      inference('cnf', [status(esa)], [l78_tops_1])).
% 5.74/5.94  thf('12', plain,
% 5.74/5.94      ((~ (l1_pre_topc @ sk_A)
% 5.74/5.94        | ((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.74/5.94               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.74/5.94      inference('sup-', [status(thm)], ['10', '11'])).
% 5.74/5.94  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('14', plain,
% 5.74/5.94      (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.74/5.94            (k1_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('demod', [status(thm)], ['12', '13'])).
% 5.74/5.94  thf('15', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['9', '14'])).
% 5.74/5.94  thf('16', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(redefinition_k7_subset_1, axiom,
% 5.74/5.94    (![A:$i,B:$i,C:$i]:
% 5.74/5.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.74/5.94       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 5.74/5.94  thf('17', plain,
% 5.74/5.94      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 5.74/5.94          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 5.74/5.94      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.74/5.94  thf('18', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.74/5.94           = (k4_xboole_0 @ sk_B @ X0))),
% 5.74/5.94      inference('sup-', [status(thm)], ['16', '17'])).
% 5.74/5.94  thf('19', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('demod', [status(thm)], ['15', '18'])).
% 5.74/5.94  thf('20', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.74/5.94           = (k4_xboole_0 @ sk_B @ X0))),
% 5.74/5.94      inference('sup-', [status(thm)], ['16', '17'])).
% 5.74/5.94  thf('21', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94              (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= (~
% 5.74/5.94             (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('split', [status(esa)], ['0'])).
% 5.74/5.94  thf('22', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= (~
% 5.74/5.94             (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup-', [status(thm)], ['20', '21'])).
% 5.74/5.94  thf('23', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 5.74/5.94         <= (~
% 5.74/5.94             (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 5.74/5.94             ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['19', '22'])).
% 5.74/5.94  thf('24', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.74/5.94       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('simplify', [status(thm)], ['23'])).
% 5.74/5.94  thf('25', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.74/5.94       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('split', [status(esa)], ['2'])).
% 5.74/5.94  thf(idempotence_k2_xboole_0, axiom,
% 5.74/5.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 5.74/5.94  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.74/5.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 5.74/5.94  thf('27', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.74/5.94           = (k4_xboole_0 @ sk_B @ X0))),
% 5.74/5.94      inference('sup-', [status(thm)], ['16', '17'])).
% 5.74/5.94  thf('28', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('split', [status(esa)], ['2'])).
% 5.74/5.94  thf('29', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['27', '28'])).
% 5.74/5.94  thf('30', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(t44_tops_1, axiom,
% 5.74/5.94    (![A:$i]:
% 5.74/5.94     ( ( l1_pre_topc @ A ) =>
% 5.74/5.94       ( ![B:$i]:
% 5.74/5.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 5.74/5.94  thf('31', plain,
% 5.74/5.94      (![X36 : $i, X37 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 5.74/5.94          | (r1_tarski @ (k1_tops_1 @ X37 @ X36) @ X36)
% 5.74/5.94          | ~ (l1_pre_topc @ X37))),
% 5.74/5.94      inference('cnf', [status(esa)], [t44_tops_1])).
% 5.74/5.94  thf('32', plain,
% 5.74/5.94      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['30', '31'])).
% 5.74/5.94  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('34', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.74/5.94      inference('demod', [status(thm)], ['32', '33'])).
% 5.74/5.94  thf(t3_subset, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.74/5.94  thf('35', plain,
% 5.74/5.94      (![X25 : $i, X27 : $i]:
% 5.74/5.94         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 5.74/5.94      inference('cnf', [status(esa)], [t3_subset])).
% 5.74/5.94  thf('36', plain,
% 5.74/5.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['34', '35'])).
% 5.74/5.94  thf(dt_k3_subset_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.74/5.94       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.74/5.94  thf('37', plain,
% 5.74/5.94      (![X13 : $i, X14 : $i]:
% 5.74/5.94         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 5.74/5.94          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 5.74/5.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 5.74/5.94  thf('38', plain,
% 5.74/5.94      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.74/5.94        (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['36', '37'])).
% 5.74/5.94  thf('39', plain,
% 5.74/5.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['34', '35'])).
% 5.74/5.94  thf(d5_subset_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.74/5.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.74/5.94  thf('40', plain,
% 5.74/5.94      (![X11 : $i, X12 : $i]:
% 5.74/5.94         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 5.74/5.94          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 5.74/5.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.74/5.94  thf('41', plain,
% 5.74/5.94      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.74/5.94         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['39', '40'])).
% 5.74/5.94  thf('42', plain,
% 5.74/5.94      ((m1_subset_1 @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.74/5.94        (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('demod', [status(thm)], ['38', '41'])).
% 5.74/5.94  thf('43', plain,
% 5.74/5.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['29', '42'])).
% 5.74/5.94  thf('44', plain,
% 5.74/5.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['34', '35'])).
% 5.74/5.94  thf(redefinition_k4_subset_1, axiom,
% 5.74/5.94    (![A:$i,B:$i,C:$i]:
% 5.74/5.94     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.74/5.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.74/5.94       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.74/5.94  thf('45', plain,
% 5.74/5.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 5.74/5.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 5.74/5.94          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 5.74/5.94      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.74/5.94  thf('46', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 5.74/5.94            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 5.74/5.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['44', '45'])).
% 5.74/5.94  thf('47', plain,
% 5.74/5.94      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94          (k2_tops_1 @ sk_A @ sk_B))
% 5.74/5.94          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94             (k2_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup-', [status(thm)], ['43', '46'])).
% 5.74/5.94  thf(commutativity_k2_tarski, axiom,
% 5.74/5.94    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.74/5.94  thf('48', plain,
% 5.74/5.94      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 5.74/5.94      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.74/5.94  thf(l51_zfmisc_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.74/5.94  thf('49', plain,
% 5.74/5.94      (![X8 : $i, X9 : $i]:
% 5.74/5.94         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 5.74/5.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.74/5.94  thf('50', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]:
% 5.74/5.94         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['48', '49'])).
% 5.74/5.94  thf('51', plain,
% 5.74/5.94      (![X8 : $i, X9 : $i]:
% 5.74/5.94         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 5.74/5.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.74/5.94  thf('52', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('53', plain,
% 5.74/5.94      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94          (k2_tops_1 @ sk_A @ sk_B))
% 5.74/5.94          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('demod', [status(thm)], ['47', '52'])).
% 5.74/5.94  thf('54', plain,
% 5.74/5.94      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['27', '28'])).
% 5.74/5.94  thf('55', plain,
% 5.74/5.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['34', '35'])).
% 5.74/5.94  thf(t25_subset_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.74/5.94       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 5.74/5.94         ( k2_subset_1 @ A ) ) ))).
% 5.74/5.94  thf('56', plain,
% 5.74/5.94      (![X21 : $i, X22 : $i]:
% 5.74/5.94         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 5.74/5.94            = (k2_subset_1 @ X21))
% 5.74/5.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 5.74/5.94      inference('cnf', [status(esa)], [t25_subset_1])).
% 5.74/5.94  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.74/5.94  thf('57', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 5.74/5.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.74/5.94  thf('58', plain,
% 5.74/5.94      (![X21 : $i, X22 : $i]:
% 5.74/5.94         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 5.74/5.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 5.74/5.94      inference('demod', [status(thm)], ['56', '57'])).
% 5.74/5.94  thf('59', plain,
% 5.74/5.94      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 5.74/5.94      inference('sup-', [status(thm)], ['55', '58'])).
% 5.74/5.94  thf('60', plain,
% 5.74/5.94      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.74/5.94         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['39', '40'])).
% 5.74/5.94  thf('61', plain,
% 5.74/5.94      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94         (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 5.74/5.94      inference('demod', [status(thm)], ['59', '60'])).
% 5.74/5.94  thf('62', plain,
% 5.74/5.94      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['54', '61'])).
% 5.74/5.94  thf('63', plain,
% 5.74/5.94      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.74/5.94          = (sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['53', '62'])).
% 5.74/5.94  thf(t4_xboole_1, axiom,
% 5.74/5.94    (![A:$i,B:$i,C:$i]:
% 5.74/5.94     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 5.74/5.94       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.74/5.94  thf('64', plain,
% 5.74/5.94      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 5.74/5.94           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 5.74/5.94      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.74/5.94  thf('65', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('66', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['64', '65'])).
% 5.74/5.94  thf('67', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.74/5.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 5.74/5.94  thf('69', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('70', plain,
% 5.74/5.94      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 5.74/5.94           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 5.74/5.94      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.74/5.94  thf('71', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['69', '70'])).
% 5.74/5.94  thf('72', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X1 @ X0)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['68', '71'])).
% 5.74/5.94  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.74/5.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 5.74/5.94  thf('74', plain,
% 5.74/5.94      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 5.74/5.94           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 5.74/5.94      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.74/5.94  thf('75', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X0 @ X1)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['73', '74'])).
% 5.74/5.94  thf('76', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X1 @ X0)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.74/5.94      inference('demod', [status(thm)], ['72', '75'])).
% 5.74/5.94  thf('77', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X0 @ X1)
% 5.74/5.94           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['67', '76'])).
% 5.74/5.94  thf('78', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 5.74/5.94           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['66', '77'])).
% 5.74/5.94  thf('79', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['69', '70'])).
% 5.74/5.94  thf('80', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 5.74/5.94           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.74/5.94      inference('demod', [status(thm)], ['78', '79'])).
% 5.74/5.94  thf('81', plain,
% 5.74/5.94      ((![X0 : $i]:
% 5.74/5.94          ((k2_xboole_0 @ X0 @ 
% 5.74/5.94            (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94             (k2_tops_1 @ sk_A @ sk_B)))
% 5.74/5.94            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94               (k2_xboole_0 @ X0 @ sk_B))))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['63', '80'])).
% 5.74/5.94  thf('82', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('83', plain,
% 5.74/5.94      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 5.74/5.94          = (sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['53', '62'])).
% 5.74/5.94  thf('84', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['69', '70'])).
% 5.74/5.94  thf('85', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('86', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['84', '85'])).
% 5.74/5.94  thf('87', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(dt_k2_tops_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( ( l1_pre_topc @ A ) & 
% 5.74/5.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.74/5.94       ( m1_subset_1 @
% 5.74/5.94         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.74/5.94  thf('88', plain,
% 5.74/5.94      (![X30 : $i, X31 : $i]:
% 5.74/5.94         (~ (l1_pre_topc @ X30)
% 5.74/5.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 5.74/5.94          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 5.74/5.94             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 5.74/5.94      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.74/5.94  thf('89', plain,
% 5.74/5.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.74/5.94        | ~ (l1_pre_topc @ sk_A))),
% 5.74/5.94      inference('sup-', [status(thm)], ['87', '88'])).
% 5.74/5.94  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('91', plain,
% 5.74/5.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.74/5.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('demod', [status(thm)], ['89', '90'])).
% 5.74/5.94  thf('92', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('93', plain,
% 5.74/5.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 5.74/5.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 5.74/5.94          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 5.74/5.94      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.74/5.94  thf('94', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.74/5.94            = (k2_xboole_0 @ sk_B @ X0))
% 5.74/5.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.74/5.94      inference('sup-', [status(thm)], ['92', '93'])).
% 5.74/5.94  thf('95', plain,
% 5.74/5.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 5.74/5.94         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('sup-', [status(thm)], ['91', '94'])).
% 5.74/5.94  thf('96', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(t65_tops_1, axiom,
% 5.74/5.94    (![A:$i]:
% 5.74/5.94     ( ( l1_pre_topc @ A ) =>
% 5.74/5.94       ( ![B:$i]:
% 5.74/5.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.74/5.94           ( ( k2_pre_topc @ A @ B ) =
% 5.74/5.94             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.74/5.94  thf('97', plain,
% 5.74/5.94      (![X38 : $i, X39 : $i]:
% 5.74/5.94         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 5.74/5.94          | ((k2_pre_topc @ X39 @ X38)
% 5.74/5.94              = (k4_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 5.74/5.94                 (k2_tops_1 @ X39 @ X38)))
% 5.74/5.94          | ~ (l1_pre_topc @ X39))),
% 5.74/5.94      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.74/5.94  thf('98', plain,
% 5.74/5.94      ((~ (l1_pre_topc @ sk_A)
% 5.74/5.94        | ((k2_pre_topc @ sk_A @ sk_B)
% 5.74/5.94            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.74/5.94      inference('sup-', [status(thm)], ['96', '97'])).
% 5.74/5.94  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('100', plain,
% 5.74/5.94      (((k2_pre_topc @ sk_A @ sk_B)
% 5.74/5.94         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('demod', [status(thm)], ['98', '99'])).
% 5.74/5.94  thf('101', plain,
% 5.74/5.94      (((k2_pre_topc @ sk_A @ sk_B)
% 5.74/5.94         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['95', '100'])).
% 5.74/5.94  thf('102', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('103', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.74/5.94           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 5.74/5.94      inference('sup+', [status(thm)], ['64', '65'])).
% 5.74/5.94  thf('104', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['50', '51'])).
% 5.74/5.94  thf('105', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.74/5.94           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 5.74/5.94      inference('sup+', [status(thm)], ['103', '104'])).
% 5.74/5.94  thf('106', plain,
% 5.74/5.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0))
% 5.74/5.94           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 5.74/5.94      inference('sup+', [status(thm)], ['102', '105'])).
% 5.74/5.94  thf('107', plain,
% 5.74/5.94      (![X0 : $i]:
% 5.74/5.94         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 5.74/5.94           = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 5.74/5.94      inference('sup+', [status(thm)], ['101', '106'])).
% 5.74/5.94  thf('108', plain,
% 5.74/5.94      ((![X0 : $i]:
% 5.74/5.94          ((k2_xboole_0 @ X0 @ sk_B)
% 5.74/5.94            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('demod', [status(thm)], ['81', '82', '83', '86', '107'])).
% 5.74/5.94  thf('109', plain,
% 5.74/5.94      ((((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 5.74/5.94          = (k2_pre_topc @ sk_A @ sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['26', '108'])).
% 5.74/5.94  thf('110', plain,
% 5.74/5.94      ((![X0 : $i]:
% 5.74/5.94          ((k2_xboole_0 @ X0 @ sk_B)
% 5.74/5.94            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('demod', [status(thm)], ['81', '82', '83', '86', '107'])).
% 5.74/5.94  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.74/5.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 5.74/5.94  thf('112', plain,
% 5.74/5.94      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('demod', [status(thm)], ['109', '110', '111'])).
% 5.74/5.94  thf('113', plain,
% 5.74/5.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf(fc1_tops_1, axiom,
% 5.74/5.94    (![A:$i,B:$i]:
% 5.74/5.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 5.74/5.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.74/5.94       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 5.74/5.94  thf('114', plain,
% 5.74/5.94      (![X32 : $i, X33 : $i]:
% 5.74/5.94         (~ (l1_pre_topc @ X32)
% 5.74/5.94          | ~ (v2_pre_topc @ X32)
% 5.74/5.94          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 5.74/5.94          | (v4_pre_topc @ (k2_pre_topc @ X32 @ X33) @ X32))),
% 5.74/5.94      inference('cnf', [status(esa)], [fc1_tops_1])).
% 5.74/5.94  thf('115', plain,
% 5.74/5.94      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 5.74/5.94        | ~ (v2_pre_topc @ sk_A)
% 5.74/5.94        | ~ (l1_pre_topc @ sk_A))),
% 5.74/5.94      inference('sup-', [status(thm)], ['113', '114'])).
% 5.74/5.94  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 5.74/5.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.74/5.94  thf('118', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 5.74/5.94      inference('demod', [status(thm)], ['115', '116', '117'])).
% 5.74/5.94  thf('119', plain,
% 5.74/5.94      (((v4_pre_topc @ sk_B @ sk_A))
% 5.74/5.94         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.74/5.94      inference('sup+', [status(thm)], ['112', '118'])).
% 5.74/5.94  thf('120', plain,
% 5.74/5.94      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.74/5.94      inference('split', [status(esa)], ['0'])).
% 5.74/5.94  thf('121', plain,
% 5.74/5.94      (~
% 5.74/5.94       (((k2_tops_1 @ sk_A @ sk_B)
% 5.74/5.94          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.74/5.94             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.74/5.94       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.74/5.94      inference('sup-', [status(thm)], ['119', '120'])).
% 5.74/5.94  thf('122', plain, ($false),
% 5.74/5.94      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '121'])).
% 5.74/5.94  
% 5.74/5.94  % SZS output end Refutation
% 5.74/5.94  
% 5.74/5.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
