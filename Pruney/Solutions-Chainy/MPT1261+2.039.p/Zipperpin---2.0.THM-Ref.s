%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Trv9ZV5l3V

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 805 expanded)
%              Number of leaves         :   40 ( 260 expanded)
%              Depth                    :   16
%              Number of atoms          : 1606 (9307 expanded)
%              Number of equality atoms :  124 ( 672 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ X36 ) @ ( k1_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k6_subset_1 @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X39 @ X38 ) @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k6_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_subset_1 @ X23 @ X24 @ ( k3_subset_1 @ X23 @ X24 ) )
        = ( k2_subset_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('60',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_subset_1 @ X23 @ X24 @ ( k3_subset_1 @ X23 @ X24 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

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
    inference('sup+',[status(thm)],['46','47'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','62'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

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
    inference('sup+',[status(thm)],['28','108'])).

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
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X34 @ X35 ) @ X34 ) ) ),
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
    inference('sat_resolution*',[status(thm)],['1','26','27','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Trv9ZV5l3V
% 0.14/0.37  % Computer   : n020.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:27:37 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.99/2.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.99/2.20  % Solved by: fo/fo7.sh
% 1.99/2.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.99/2.20  % done 1996 iterations in 1.756s
% 1.99/2.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.99/2.20  % SZS output start Refutation
% 1.99/2.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.99/2.20  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.99/2.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.99/2.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.99/2.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.99/2.20  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.99/2.20  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.99/2.20  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.99/2.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.99/2.20  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.99/2.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.99/2.20  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.99/2.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.99/2.20  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.99/2.20  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.99/2.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.99/2.20  thf(sk_B_type, type, sk_B: $i).
% 1.99/2.20  thf(sk_A_type, type, sk_A: $i).
% 1.99/2.20  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.99/2.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.99/2.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.99/2.20  thf(t77_tops_1, conjecture,
% 1.99/2.20    (![A:$i]:
% 1.99/2.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.99/2.20       ( ![B:$i]:
% 1.99/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20           ( ( v4_pre_topc @ B @ A ) <=>
% 1.99/2.20             ( ( k2_tops_1 @ A @ B ) =
% 1.99/2.20               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.99/2.20  thf(zf_stmt_0, negated_conjecture,
% 1.99/2.20    (~( ![A:$i]:
% 1.99/2.20        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.99/2.20          ( ![B:$i]:
% 1.99/2.20            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20              ( ( v4_pre_topc @ B @ A ) <=>
% 1.99/2.20                ( ( k2_tops_1 @ A @ B ) =
% 1.99/2.20                  ( k7_subset_1 @
% 1.99/2.20                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.99/2.20    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.99/2.20  thf('0', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20              (k1_tops_1 @ sk_A @ sk_B)))
% 1.99/2.20        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('1', plain,
% 1.99/2.20      (~
% 1.99/2.20       (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.99/2.20       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('split', [status(esa)], ['0'])).
% 1.99/2.20  thf('2', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B)))
% 1.99/2.20        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('3', plain,
% 1.99/2.20      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('split', [status(esa)], ['2'])).
% 1.99/2.20  thf('4', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(t52_pre_topc, axiom,
% 1.99/2.20    (![A:$i]:
% 1.99/2.20     ( ( l1_pre_topc @ A ) =>
% 1.99/2.20       ( ![B:$i]:
% 1.99/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.99/2.20             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.99/2.20               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.99/2.20  thf('5', plain,
% 1.99/2.20      (![X30 : $i, X31 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.99/2.20          | ~ (v4_pre_topc @ X30 @ X31)
% 1.99/2.20          | ((k2_pre_topc @ X31 @ X30) = (X30))
% 1.99/2.20          | ~ (l1_pre_topc @ X31))),
% 1.99/2.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.99/2.20  thf('6', plain,
% 1.99/2.20      ((~ (l1_pre_topc @ sk_A)
% 1.99/2.20        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.99/2.20        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('sup-', [status(thm)], ['4', '5'])).
% 1.99/2.20  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('8', plain,
% 1.99/2.20      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('demod', [status(thm)], ['6', '7'])).
% 1.99/2.20  thf('9', plain,
% 1.99/2.20      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.99/2.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('sup-', [status(thm)], ['3', '8'])).
% 1.99/2.20  thf('10', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(l78_tops_1, axiom,
% 1.99/2.20    (![A:$i]:
% 1.99/2.20     ( ( l1_pre_topc @ A ) =>
% 1.99/2.20       ( ![B:$i]:
% 1.99/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20           ( ( k2_tops_1 @ A @ B ) =
% 1.99/2.20             ( k7_subset_1 @
% 1.99/2.20               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.99/2.20               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.99/2.20  thf('11', plain,
% 1.99/2.20      (![X36 : $i, X37 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.99/2.20          | ((k2_tops_1 @ X37 @ X36)
% 1.99/2.20              = (k7_subset_1 @ (u1_struct_0 @ X37) @ 
% 1.99/2.20                 (k2_pre_topc @ X37 @ X36) @ (k1_tops_1 @ X37 @ X36)))
% 1.99/2.20          | ~ (l1_pre_topc @ X37))),
% 1.99/2.20      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.99/2.20  thf('12', plain,
% 1.99/2.20      ((~ (l1_pre_topc @ sk_A)
% 1.99/2.20        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.99/2.20               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.99/2.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.99/2.20  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('14', plain,
% 1.99/2.20      (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.99/2.20            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.99/2.20      inference('demod', [status(thm)], ['12', '13'])).
% 1.99/2.20  thf('15', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['9', '14'])).
% 1.99/2.20  thf('16', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(redefinition_k7_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i,C:$i]:
% 1.99/2.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.99/2.20       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.99/2.20  thf('17', plain,
% 1.99/2.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.99/2.20          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 1.99/2.20      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.99/2.20  thf(redefinition_k6_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.99/2.20  thf('18', plain,
% 1.99/2.20      (![X18 : $i, X19 : $i]:
% 1.99/2.20         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.99/2.20      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.99/2.20  thf('19', plain,
% 1.99/2.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.99/2.20          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k6_subset_1 @ X20 @ X22)))),
% 1.99/2.20      inference('demod', [status(thm)], ['17', '18'])).
% 1.99/2.20  thf('20', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.99/2.20           = (k6_subset_1 @ sk_B @ X0))),
% 1.99/2.20      inference('sup-', [status(thm)], ['16', '19'])).
% 1.99/2.20  thf('21', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('demod', [status(thm)], ['15', '20'])).
% 1.99/2.20  thf('22', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.99/2.20           = (k6_subset_1 @ sk_B @ X0))),
% 1.99/2.20      inference('sup-', [status(thm)], ['16', '19'])).
% 1.99/2.20  thf('23', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20              (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= (~
% 1.99/2.20             (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('split', [status(esa)], ['0'])).
% 1.99/2.20  thf('24', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= (~
% 1.99/2.20             (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup-', [status(thm)], ['22', '23'])).
% 1.99/2.20  thf('25', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.99/2.20         <= (~
% 1.99/2.20             (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.99/2.20             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('sup-', [status(thm)], ['21', '24'])).
% 1.99/2.20  thf('26', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.99/2.20       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('simplify', [status(thm)], ['25'])).
% 1.99/2.20  thf('27', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.99/2.20       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('split', [status(esa)], ['2'])).
% 1.99/2.20  thf(idempotence_k2_xboole_0, axiom,
% 1.99/2.20    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.99/2.20  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.99/2.20      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.99/2.20  thf('29', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.99/2.20           = (k6_subset_1 @ sk_B @ X0))),
% 1.99/2.20      inference('sup-', [status(thm)], ['16', '19'])).
% 1.99/2.20  thf('30', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('split', [status(esa)], ['2'])).
% 1.99/2.20  thf('31', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['29', '30'])).
% 1.99/2.20  thf(dt_k6_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.99/2.20  thf('32', plain,
% 1.99/2.20      (![X13 : $i, X14 : $i]:
% 1.99/2.20         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 1.99/2.20      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.99/2.20  thf('33', plain,
% 1.99/2.20      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['31', '32'])).
% 1.99/2.20  thf('34', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(t44_tops_1, axiom,
% 1.99/2.20    (![A:$i]:
% 1.99/2.20     ( ( l1_pre_topc @ A ) =>
% 1.99/2.20       ( ![B:$i]:
% 1.99/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.99/2.20  thf('35', plain,
% 1.99/2.20      (![X38 : $i, X39 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.99/2.20          | (r1_tarski @ (k1_tops_1 @ X39 @ X38) @ X38)
% 1.99/2.20          | ~ (l1_pre_topc @ X39))),
% 1.99/2.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.99/2.20  thf('36', plain,
% 1.99/2.20      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.99/2.20      inference('sup-', [status(thm)], ['34', '35'])).
% 1.99/2.20  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('38', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.99/2.20      inference('demod', [status(thm)], ['36', '37'])).
% 1.99/2.20  thf(t3_subset, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.99/2.20  thf('39', plain,
% 1.99/2.20      (![X27 : $i, X29 : $i]:
% 1.99/2.20         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 1.99/2.20      inference('cnf', [status(esa)], [t3_subset])).
% 1.99/2.20  thf('40', plain,
% 1.99/2.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.99/2.20      inference('sup-', [status(thm)], ['38', '39'])).
% 1.99/2.20  thf(redefinition_k4_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i,C:$i]:
% 1.99/2.20     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.99/2.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.99/2.20       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.99/2.20  thf('41', plain,
% 1.99/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.99/2.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 1.99/2.20          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 1.99/2.20      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.99/2.20  thf('42', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.99/2.20            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.99/2.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.99/2.20      inference('sup-', [status(thm)], ['40', '41'])).
% 1.99/2.20  thf('43', plain,
% 1.99/2.20      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20          (k2_tops_1 @ sk_A @ sk_B))
% 1.99/2.20          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20             (k2_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup-', [status(thm)], ['33', '42'])).
% 1.99/2.20  thf(commutativity_k2_tarski, axiom,
% 1.99/2.20    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.99/2.20  thf('44', plain,
% 1.99/2.20      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 1.99/2.20      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.99/2.20  thf(l51_zfmisc_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.99/2.20  thf('45', plain,
% 1.99/2.20      (![X8 : $i, X9 : $i]:
% 1.99/2.20         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 1.99/2.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.99/2.20  thf('46', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]:
% 1.99/2.20         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['44', '45'])).
% 1.99/2.20  thf('47', plain,
% 1.99/2.20      (![X8 : $i, X9 : $i]:
% 1.99/2.20         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 1.99/2.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.99/2.20  thf('48', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('49', plain,
% 1.99/2.20      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20          (k2_tops_1 @ sk_A @ sk_B))
% 1.99/2.20          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('demod', [status(thm)], ['43', '48'])).
% 1.99/2.20  thf('50', plain,
% 1.99/2.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.99/2.20      inference('sup-', [status(thm)], ['38', '39'])).
% 1.99/2.20  thf(d5_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.99/2.20       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.99/2.20  thf('51', plain,
% 1.99/2.20      (![X11 : $i, X12 : $i]:
% 1.99/2.20         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.99/2.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.99/2.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.99/2.20  thf('52', plain,
% 1.99/2.20      (![X18 : $i, X19 : $i]:
% 1.99/2.20         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.99/2.20      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.99/2.20  thf('53', plain,
% 1.99/2.20      (![X11 : $i, X12 : $i]:
% 1.99/2.20         (((k3_subset_1 @ X11 @ X12) = (k6_subset_1 @ X11 @ X12))
% 1.99/2.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.99/2.20      inference('demod', [status(thm)], ['51', '52'])).
% 1.99/2.20  thf('54', plain,
% 1.99/2.20      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.99/2.20         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.99/2.20      inference('sup-', [status(thm)], ['50', '53'])).
% 1.99/2.20  thf('55', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['29', '30'])).
% 1.99/2.20  thf('56', plain,
% 1.99/2.20      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['54', '55'])).
% 1.99/2.20  thf('57', plain,
% 1.99/2.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.99/2.20      inference('sup-', [status(thm)], ['38', '39'])).
% 1.99/2.20  thf(t25_subset_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.99/2.20       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.99/2.20         ( k2_subset_1 @ A ) ) ))).
% 1.99/2.20  thf('58', plain,
% 1.99/2.20      (![X23 : $i, X24 : $i]:
% 1.99/2.20         (((k4_subset_1 @ X23 @ X24 @ (k3_subset_1 @ X23 @ X24))
% 1.99/2.20            = (k2_subset_1 @ X23))
% 1.99/2.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 1.99/2.20      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.99/2.20  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.99/2.20  thf('59', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 1.99/2.20      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.99/2.20  thf('60', plain,
% 1.99/2.20      (![X23 : $i, X24 : $i]:
% 1.99/2.20         (((k4_subset_1 @ X23 @ X24 @ (k3_subset_1 @ X23 @ X24)) = (X23))
% 1.99/2.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 1.99/2.20      inference('demod', [status(thm)], ['58', '59'])).
% 1.99/2.20  thf('61', plain,
% 1.99/2.20      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.99/2.20      inference('sup-', [status(thm)], ['57', '60'])).
% 1.99/2.20  thf('62', plain,
% 1.99/2.20      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['56', '61'])).
% 1.99/2.20  thf('63', plain,
% 1.99/2.20      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.99/2.20          = (sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['49', '62'])).
% 1.99/2.20  thf('64', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf(t4_xboole_1, axiom,
% 1.99/2.20    (![A:$i,B:$i,C:$i]:
% 1.99/2.20     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.99/2.20       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.99/2.20  thf('65', plain,
% 1.99/2.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 1.99/2.20           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 1.99/2.20      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.99/2.20  thf('66', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.99/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['64', '65'])).
% 1.99/2.20  thf('67', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.99/2.20      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.99/2.20  thf('69', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('70', plain,
% 1.99/2.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 1.99/2.20           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 1.99/2.20      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.99/2.20  thf('71', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['69', '70'])).
% 1.99/2.20  thf('72', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X1 @ X0)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['68', '71'])).
% 1.99/2.20  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.99/2.20      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.99/2.20  thf('74', plain,
% 1.99/2.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 1.99/2.20           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 1.99/2.20      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.99/2.20  thf('75', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['73', '74'])).
% 1.99/2.20  thf('76', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X1 @ X0)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.99/2.20      inference('demod', [status(thm)], ['72', '75'])).
% 1.99/2.20  thf('77', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.99/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['67', '76'])).
% 1.99/2.20  thf('78', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 1.99/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['66', '77'])).
% 1.99/2.20  thf('79', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['69', '70'])).
% 1.99/2.20  thf('80', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 1.99/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.99/2.20      inference('demod', [status(thm)], ['78', '79'])).
% 1.99/2.20  thf('81', plain,
% 1.99/2.20      ((![X0 : $i]:
% 1.99/2.20          ((k2_xboole_0 @ X0 @ 
% 1.99/2.20            (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20             (k2_tops_1 @ sk_A @ sk_B)))
% 1.99/2.20            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20               (k2_xboole_0 @ X0 @ sk_B))))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['63', '80'])).
% 1.99/2.20  thf('82', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('83', plain,
% 1.99/2.20      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.99/2.20          = (sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['49', '62'])).
% 1.99/2.20  thf('84', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.99/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['69', '70'])).
% 1.99/2.20  thf('85', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('86', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 1.99/2.20           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['84', '85'])).
% 1.99/2.20  thf('87', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(dt_k2_tops_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( ( l1_pre_topc @ A ) & 
% 1.99/2.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.99/2.20       ( m1_subset_1 @
% 1.99/2.20         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.99/2.20  thf('88', plain,
% 1.99/2.20      (![X32 : $i, X33 : $i]:
% 1.99/2.20         (~ (l1_pre_topc @ X32)
% 1.99/2.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.99/2.20          | (m1_subset_1 @ (k2_tops_1 @ X32 @ X33) @ 
% 1.99/2.20             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 1.99/2.20      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.99/2.20  thf('89', plain,
% 1.99/2.20      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.99/2.20        | ~ (l1_pre_topc @ sk_A))),
% 1.99/2.20      inference('sup-', [status(thm)], ['87', '88'])).
% 1.99/2.20  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('91', plain,
% 1.99/2.20      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('demod', [status(thm)], ['89', '90'])).
% 1.99/2.20  thf('92', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('93', plain,
% 1.99/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.99/2.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 1.99/2.20          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 1.99/2.20      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.99/2.20  thf('94', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.99/2.20            = (k2_xboole_0 @ sk_B @ X0))
% 1.99/2.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.99/2.20      inference('sup-', [status(thm)], ['92', '93'])).
% 1.99/2.20  thf('95', plain,
% 1.99/2.20      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.99/2.20         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.99/2.20      inference('sup-', [status(thm)], ['91', '94'])).
% 1.99/2.20  thf('96', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(t65_tops_1, axiom,
% 1.99/2.20    (![A:$i]:
% 1.99/2.20     ( ( l1_pre_topc @ A ) =>
% 1.99/2.20       ( ![B:$i]:
% 1.99/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.99/2.20           ( ( k2_pre_topc @ A @ B ) =
% 1.99/2.20             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.99/2.20  thf('97', plain,
% 1.99/2.20      (![X40 : $i, X41 : $i]:
% 1.99/2.20         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.99/2.20          | ((k2_pre_topc @ X41 @ X40)
% 1.99/2.20              = (k4_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 1.99/2.20                 (k2_tops_1 @ X41 @ X40)))
% 1.99/2.20          | ~ (l1_pre_topc @ X41))),
% 1.99/2.20      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.99/2.20  thf('98', plain,
% 1.99/2.20      ((~ (l1_pre_topc @ sk_A)
% 1.99/2.20        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.99/2.20            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.99/2.20      inference('sup-', [status(thm)], ['96', '97'])).
% 1.99/2.20  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('100', plain,
% 1.99/2.20      (((k2_pre_topc @ sk_A @ sk_B)
% 1.99/2.20         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.99/2.20      inference('demod', [status(thm)], ['98', '99'])).
% 1.99/2.20  thf('101', plain,
% 1.99/2.20      (((k2_pre_topc @ sk_A @ sk_B)
% 1.99/2.20         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['95', '100'])).
% 1.99/2.20  thf('102', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.99/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['64', '65'])).
% 1.99/2.20  thf('103', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.99/2.20      inference('sup+', [status(thm)], ['46', '47'])).
% 1.99/2.20  thf('104', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 1.99/2.20           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['102', '103'])).
% 1.99/2.20  thf('105', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 1.99/2.20           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.99/2.20              (k2_xboole_0 @ X0 @ sk_B)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['101', '104'])).
% 1.99/2.20  thf('106', plain,
% 1.99/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 1.99/2.20           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.99/2.20      inference('sup+', [status(thm)], ['84', '85'])).
% 1.99/2.20  thf('107', plain,
% 1.99/2.20      (![X0 : $i]:
% 1.99/2.20         ((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 1.99/2.20           = (k2_xboole_0 @ sk_B @ 
% 1.99/2.20              (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.99/2.20      inference('demod', [status(thm)], ['105', '106'])).
% 1.99/2.20  thf('108', plain,
% 1.99/2.20      ((![X0 : $i]:
% 1.99/2.20          ((k2_xboole_0 @ X0 @ sk_B)
% 1.99/2.20            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('demod', [status(thm)], ['81', '82', '83', '86', '107'])).
% 1.99/2.20  thf('109', plain,
% 1.99/2.20      ((((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 1.99/2.20          = (k2_pre_topc @ sk_A @ sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['28', '108'])).
% 1.99/2.20  thf('110', plain,
% 1.99/2.20      ((![X0 : $i]:
% 1.99/2.20          ((k2_xboole_0 @ X0 @ sk_B)
% 1.99/2.20            = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('demod', [status(thm)], ['81', '82', '83', '86', '107'])).
% 1.99/2.20  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.99/2.20      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.99/2.20  thf('112', plain,
% 1.99/2.20      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.99/2.20  thf('113', plain,
% 1.99/2.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf(fc1_tops_1, axiom,
% 1.99/2.20    (![A:$i,B:$i]:
% 1.99/2.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.99/2.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.99/2.20       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.99/2.20  thf('114', plain,
% 1.99/2.20      (![X34 : $i, X35 : $i]:
% 1.99/2.20         (~ (l1_pre_topc @ X34)
% 1.99/2.20          | ~ (v2_pre_topc @ X34)
% 1.99/2.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.99/2.20          | (v4_pre_topc @ (k2_pre_topc @ X34 @ X35) @ X34))),
% 1.99/2.20      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.99/2.20  thf('115', plain,
% 1.99/2.20      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.99/2.20        | ~ (v2_pre_topc @ sk_A)
% 1.99/2.20        | ~ (l1_pre_topc @ sk_A))),
% 1.99/2.20      inference('sup-', [status(thm)], ['113', '114'])).
% 1.99/2.20  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.20  thf('118', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.99/2.20      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.99/2.20  thf('119', plain,
% 1.99/2.20      (((v4_pre_topc @ sk_B @ sk_A))
% 1.99/2.20         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.99/2.20      inference('sup+', [status(thm)], ['112', '118'])).
% 1.99/2.20  thf('120', plain,
% 1.99/2.20      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.99/2.20      inference('split', [status(esa)], ['0'])).
% 1.99/2.20  thf('121', plain,
% 1.99/2.20      (~
% 1.99/2.20       (((k2_tops_1 @ sk_A @ sk_B)
% 1.99/2.20          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.99/2.20             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.99/2.20       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.99/2.20      inference('sup-', [status(thm)], ['119', '120'])).
% 1.99/2.20  thf('122', plain, ($false),
% 1.99/2.20      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '121'])).
% 1.99/2.20  
% 1.99/2.20  % SZS output end Refutation
% 1.99/2.20  
% 1.99/2.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
