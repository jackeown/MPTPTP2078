%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eIj4K9vwsW

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:40 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 340 expanded)
%              Number of leaves         :   42 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          : 1308 (3761 expanded)
%              Number of equality atoms :   96 ( 273 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k6_subset_1 @ X28 @ X30 ) ) ) ),
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

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X22 @ ( k3_subset_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','35'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ ( k6_subset_1 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','43'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X18 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('54',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_pre_topc @ X47 @ X46 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['50','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','44','49'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','44','49'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k4_subset_1 @ X24 @ X23 @ X25 )
        = ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X22 @ ( k3_subset_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('89',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','43'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','89','90'])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('93',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('96',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X40 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('97',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','100'])).

thf('102',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eIj4K9vwsW
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.18/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.39  % Solved by: fo/fo7.sh
% 1.18/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.39  % done 2850 iterations in 0.939s
% 1.18/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.39  % SZS output start Refutation
% 1.18/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.39  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.18/1.39  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.18/1.39  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.18/1.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.18/1.39  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.18/1.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.39  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.18/1.39  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.18/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.39  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.18/1.39  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.18/1.39  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.18/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.18/1.39  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.18/1.39  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.18/1.39  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.18/1.39  thf(t77_tops_1, conjecture,
% 1.18/1.39    (![A:$i]:
% 1.18/1.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.39       ( ![B:$i]:
% 1.18/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.39           ( ( v4_pre_topc @ B @ A ) <=>
% 1.18/1.39             ( ( k2_tops_1 @ A @ B ) =
% 1.18/1.39               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.18/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.39    (~( ![A:$i]:
% 1.18/1.39        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.39          ( ![B:$i]:
% 1.18/1.39            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.39              ( ( v4_pre_topc @ B @ A ) <=>
% 1.18/1.39                ( ( k2_tops_1 @ A @ B ) =
% 1.18/1.39                  ( k7_subset_1 @
% 1.18/1.39                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.18/1.39    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.18/1.39  thf('0', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39              (k1_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('1', plain,
% 1.18/1.39      (~
% 1.18/1.39       (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.18/1.39       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('split', [status(esa)], ['0'])).
% 1.18/1.39  thf('2', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('3', plain,
% 1.18/1.39      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('split', [status(esa)], ['2'])).
% 1.18/1.39  thf('4', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(t52_pre_topc, axiom,
% 1.18/1.39    (![A:$i]:
% 1.18/1.39     ( ( l1_pre_topc @ A ) =>
% 1.18/1.39       ( ![B:$i]:
% 1.18/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.39           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.18/1.39             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.18/1.39               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.18/1.39  thf('5', plain,
% 1.18/1.39      (![X36 : $i, X37 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.18/1.39          | ~ (v4_pre_topc @ X36 @ X37)
% 1.18/1.39          | ((k2_pre_topc @ X37 @ X36) = (X36))
% 1.18/1.39          | ~ (l1_pre_topc @ X37))),
% 1.18/1.39      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.18/1.39  thf('6', plain,
% 1.18/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.39        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.18/1.39        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['4', '5'])).
% 1.18/1.39  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('8', plain,
% 1.18/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('demod', [status(thm)], ['6', '7'])).
% 1.18/1.39  thf('9', plain,
% 1.18/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.18/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['3', '8'])).
% 1.18/1.39  thf('10', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(l78_tops_1, axiom,
% 1.18/1.39    (![A:$i]:
% 1.18/1.39     ( ( l1_pre_topc @ A ) =>
% 1.18/1.39       ( ![B:$i]:
% 1.18/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.39           ( ( k2_tops_1 @ A @ B ) =
% 1.18/1.39             ( k7_subset_1 @
% 1.18/1.39               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.18/1.39               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.18/1.39  thf('11', plain,
% 1.18/1.39      (![X42 : $i, X43 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.18/1.39          | ((k2_tops_1 @ X43 @ X42)
% 1.18/1.39              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 1.18/1.39                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 1.18/1.39          | ~ (l1_pre_topc @ X43))),
% 1.18/1.39      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.18/1.39  thf('12', plain,
% 1.18/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.39        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.39               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['10', '11'])).
% 1.18/1.39  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('14', plain,
% 1.18/1.39      (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.18/1.39            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.18/1.39      inference('demod', [status(thm)], ['12', '13'])).
% 1.18/1.39  thf('15', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('sup+', [status(thm)], ['9', '14'])).
% 1.18/1.39  thf('16', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(redefinition_k7_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.39       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.18/1.39  thf('17', plain,
% 1.18/1.39      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.18/1.39          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.18/1.39  thf(redefinition_k6_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.18/1.39  thf('18', plain,
% 1.18/1.39      (![X26 : $i, X27 : $i]:
% 1.18/1.39         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.18/1.39  thf('19', plain,
% 1.18/1.39      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.18/1.39          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k6_subset_1 @ X28 @ X30)))),
% 1.18/1.39      inference('demod', [status(thm)], ['17', '18'])).
% 1.18/1.39  thf('20', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.18/1.39           = (k6_subset_1 @ sk_B @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['16', '19'])).
% 1.18/1.39  thf('21', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('demod', [status(thm)], ['15', '20'])).
% 1.18/1.39  thf('22', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.18/1.39           = (k6_subset_1 @ sk_B @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['16', '19'])).
% 1.18/1.39  thf('23', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39              (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= (~
% 1.18/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('split', [status(esa)], ['0'])).
% 1.18/1.39  thf('24', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= (~
% 1.18/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['22', '23'])).
% 1.18/1.39  thf('25', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39         <= (~
% 1.18/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.18/1.39             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['21', '24'])).
% 1.18/1.39  thf('26', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.18/1.39       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('simplify', [status(thm)], ['25'])).
% 1.18/1.39  thf('27', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.18/1.39       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('split', [status(esa)], ['2'])).
% 1.18/1.39  thf('28', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(involutiveness_k3_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.39       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.18/1.39  thf('29', plain,
% 1.18/1.39      (![X21 : $i, X22 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X22 @ (k3_subset_1 @ X22 @ X21)) = (X21))
% 1.18/1.39          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 1.18/1.39      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.18/1.39  thf('30', plain,
% 1.18/1.39      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.39         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.18/1.39      inference('sup-', [status(thm)], ['28', '29'])).
% 1.18/1.39  thf('31', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(d5_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.39       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.18/1.39  thf('32', plain,
% 1.18/1.39      (![X16 : $i, X17 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 1.18/1.39          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.39      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.18/1.39  thf('33', plain,
% 1.18/1.39      (![X26 : $i, X27 : $i]:
% 1.18/1.39         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.18/1.39  thf('34', plain,
% 1.18/1.39      (![X16 : $i, X17 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 1.18/1.39          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.39      inference('demod', [status(thm)], ['32', '33'])).
% 1.18/1.39  thf('35', plain,
% 1.18/1.39      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.18/1.39         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.18/1.39      inference('sup-', [status(thm)], ['31', '34'])).
% 1.18/1.39  thf('36', plain,
% 1.18/1.39      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.39         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['30', '35'])).
% 1.18/1.39  thf(dt_k6_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.18/1.39  thf('37', plain,
% 1.18/1.39      (![X19 : $i, X20 : $i]:
% 1.18/1.39         (m1_subset_1 @ (k6_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))),
% 1.18/1.39      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.18/1.39  thf('38', plain,
% 1.18/1.39      (![X16 : $i, X17 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 1.18/1.39          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.39      inference('demod', [status(thm)], ['32', '33'])).
% 1.18/1.39  thf('39', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.18/1.39           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['37', '38'])).
% 1.18/1.39  thf(t48_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.39  thf('40', plain,
% 1.18/1.39      (![X9 : $i, X10 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.18/1.39           = (k3_xboole_0 @ X9 @ X10))),
% 1.18/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.39  thf('41', plain,
% 1.18/1.39      (![X26 : $i, X27 : $i]:
% 1.18/1.39         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.18/1.39  thf('42', plain,
% 1.18/1.39      (![X26 : $i, X27 : $i]:
% 1.18/1.39         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.18/1.39  thf('43', plain,
% 1.18/1.39      (![X9 : $i, X10 : $i]:
% 1.18/1.39         ((k6_subset_1 @ X9 @ (k6_subset_1 @ X9 @ X10))
% 1.18/1.39           = (k3_xboole_0 @ X9 @ X10))),
% 1.18/1.39      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.18/1.39  thf('44', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.18/1.39           = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('demod', [status(thm)], ['39', '43'])).
% 1.18/1.39  thf(commutativity_k2_tarski, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.18/1.39  thf('45', plain,
% 1.18/1.39      (![X11 : $i, X12 : $i]:
% 1.18/1.39         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 1.18/1.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.18/1.39  thf(t12_setfam_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.39  thf('46', plain,
% 1.18/1.39      (![X31 : $i, X32 : $i]:
% 1.18/1.39         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 1.18/1.39      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.18/1.39  thf('47', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('sup+', [status(thm)], ['45', '46'])).
% 1.18/1.39  thf('48', plain,
% 1.18/1.39      (![X31 : $i, X32 : $i]:
% 1.18/1.39         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 1.18/1.39      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.18/1.39  thf('49', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('sup+', [status(thm)], ['47', '48'])).
% 1.18/1.39  thf('50', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['36', '44', '49'])).
% 1.18/1.39  thf('51', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('sup+', [status(thm)], ['47', '48'])).
% 1.18/1.39  thf(t22_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.18/1.39  thf('52', plain,
% 1.18/1.39      (![X5 : $i, X6 : $i]:
% 1.18/1.39         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 1.18/1.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.18/1.39  thf(dt_k2_subset_1, axiom,
% 1.18/1.39    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.18/1.39  thf('53', plain,
% 1.18/1.39      (![X18 : $i]: (m1_subset_1 @ (k2_subset_1 @ X18) @ (k1_zfmisc_1 @ X18))),
% 1.18/1.39      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.18/1.39  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.18/1.39  thf('54', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 1.18/1.39      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.18/1.39  thf('55', plain, (![X18 : $i]: (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X18))),
% 1.18/1.39      inference('demod', [status(thm)], ['53', '54'])).
% 1.18/1.39  thf(t3_subset, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.18/1.39  thf('56', plain,
% 1.18/1.39      (![X33 : $i, X34 : $i]:
% 1.18/1.39         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.18/1.39      inference('cnf', [status(esa)], [t3_subset])).
% 1.18/1.39  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.18/1.39      inference('sup-', [status(thm)], ['55', '56'])).
% 1.18/1.39  thf(t10_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.18/1.39  thf('58', plain,
% 1.18/1.39      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.39         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.18/1.39      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.18/1.39  thf('59', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['57', '58'])).
% 1.18/1.39  thf('60', plain,
% 1.18/1.39      (![X33 : $i, X35 : $i]:
% 1.18/1.39         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 1.18/1.39      inference('cnf', [status(esa)], [t3_subset])).
% 1.18/1.39  thf('61', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['59', '60'])).
% 1.18/1.39  thf('62', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.18/1.39      inference('sup+', [status(thm)], ['52', '61'])).
% 1.18/1.39  thf('63', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.18/1.39      inference('sup+', [status(thm)], ['51', '62'])).
% 1.18/1.39  thf(t65_tops_1, axiom,
% 1.18/1.39    (![A:$i]:
% 1.18/1.39     ( ( l1_pre_topc @ A ) =>
% 1.18/1.39       ( ![B:$i]:
% 1.18/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.39           ( ( k2_pre_topc @ A @ B ) =
% 1.18/1.39             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.18/1.39  thf('64', plain,
% 1.18/1.39      (![X46 : $i, X47 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.18/1.39          | ((k2_pre_topc @ X47 @ X46)
% 1.18/1.39              = (k4_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 1.18/1.39                 (k2_tops_1 @ X47 @ X46)))
% 1.18/1.39          | ~ (l1_pre_topc @ X47))),
% 1.18/1.39      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.18/1.39  thf('65', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (~ (l1_pre_topc @ X0)
% 1.18/1.39          | ((k2_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 1.18/1.39              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.18/1.39                 (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 1.18/1.39                 (k2_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.39  thf('66', plain,
% 1.18/1.39      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 1.18/1.39          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k2_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))))
% 1.18/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.18/1.39      inference('sup+', [status(thm)], ['50', '65'])).
% 1.18/1.39  thf('67', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['36', '44', '49'])).
% 1.18/1.39  thf('68', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['36', '44', '49'])).
% 1.18/1.39  thf('69', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(dt_k2_tops_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ( l1_pre_topc @ A ) & 
% 1.18/1.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.18/1.39       ( m1_subset_1 @
% 1.18/1.39         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.18/1.39  thf('70', plain,
% 1.18/1.39      (![X38 : $i, X39 : $i]:
% 1.18/1.39         (~ (l1_pre_topc @ X38)
% 1.18/1.39          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.18/1.39          | (m1_subset_1 @ (k2_tops_1 @ X38 @ X39) @ 
% 1.18/1.39             (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 1.18/1.39      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.18/1.39  thf('71', plain,
% 1.18/1.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.18/1.39         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['69', '70'])).
% 1.18/1.39  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('73', plain,
% 1.18/1.39      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.18/1.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('demod', [status(thm)], ['71', '72'])).
% 1.18/1.39  thf('74', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(redefinition_k4_subset_1, axiom,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.18/1.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.18/1.39       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.18/1.39  thf('75', plain,
% 1.18/1.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.39         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.18/1.39          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 1.18/1.39          | ((k4_subset_1 @ X24 @ X23 @ X25) = (k2_xboole_0 @ X23 @ X25)))),
% 1.18/1.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.18/1.39  thf('76', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.18/1.39            = (k2_xboole_0 @ sk_B @ X0))
% 1.18/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['74', '75'])).
% 1.18/1.39  thf('77', plain,
% 1.18/1.39      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.18/1.39         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['73', '76'])).
% 1.18/1.39  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('79', plain,
% 1.18/1.39      (((k2_pre_topc @ sk_A @ sk_B)
% 1.18/1.39         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.18/1.39      inference('demod', [status(thm)], ['66', '67', '68', '77', '78'])).
% 1.18/1.39  thf('80', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.18/1.39           = (k6_subset_1 @ sk_B @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['16', '19'])).
% 1.18/1.39  thf('81', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('split', [status(esa)], ['2'])).
% 1.18/1.39  thf('82', plain,
% 1.18/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['80', '81'])).
% 1.18/1.39  thf('83', plain,
% 1.18/1.39      (![X19 : $i, X20 : $i]:
% 1.18/1.39         (m1_subset_1 @ (k6_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))),
% 1.18/1.39      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.18/1.39  thf('84', plain,
% 1.18/1.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['82', '83'])).
% 1.18/1.39  thf('85', plain,
% 1.18/1.39      (![X21 : $i, X22 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X22 @ (k3_subset_1 @ X22 @ X21)) = (X21))
% 1.18/1.39          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 1.18/1.39      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.18/1.39  thf('86', plain,
% 1.18/1.39      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['84', '85'])).
% 1.18/1.39  thf('87', plain,
% 1.18/1.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['82', '83'])).
% 1.18/1.39  thf('88', plain,
% 1.18/1.39      (![X16 : $i, X17 : $i]:
% 1.18/1.39         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 1.18/1.39          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.39      inference('demod', [status(thm)], ['32', '33'])).
% 1.18/1.39  thf('89', plain,
% 1.18/1.39      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.18/1.39          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['87', '88'])).
% 1.18/1.39  thf('90', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.18/1.39           = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('demod', [status(thm)], ['39', '43'])).
% 1.18/1.39  thf('91', plain,
% 1.18/1.39      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.18/1.39          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('demod', [status(thm)], ['86', '89', '90'])).
% 1.18/1.39  thf('92', plain,
% 1.18/1.39      (![X5 : $i, X6 : $i]:
% 1.18/1.39         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 1.18/1.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.18/1.39  thf('93', plain,
% 1.18/1.39      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['91', '92'])).
% 1.18/1.39  thf('94', plain,
% 1.18/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['79', '93'])).
% 1.18/1.39  thf('95', plain,
% 1.18/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(fc1_tops_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.18/1.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.18/1.39       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.18/1.39  thf('96', plain,
% 1.18/1.39      (![X40 : $i, X41 : $i]:
% 1.18/1.39         (~ (l1_pre_topc @ X40)
% 1.18/1.39          | ~ (v2_pre_topc @ X40)
% 1.18/1.39          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.18/1.39          | (v4_pre_topc @ (k2_pre_topc @ X40 @ X41) @ X40))),
% 1.18/1.39      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.18/1.39  thf('97', plain,
% 1.18/1.39      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.18/1.39        | ~ (v2_pre_topc @ sk_A)
% 1.18/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['95', '96'])).
% 1.18/1.39  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('100', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.18/1.39      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.18/1.39  thf('101', plain,
% 1.18/1.39      (((v4_pre_topc @ sk_B @ sk_A))
% 1.18/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.18/1.39      inference('sup+', [status(thm)], ['94', '100'])).
% 1.18/1.39  thf('102', plain,
% 1.18/1.39      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.18/1.39      inference('split', [status(esa)], ['0'])).
% 1.18/1.39  thf('103', plain,
% 1.18/1.39      (~
% 1.18/1.39       (((k2_tops_1 @ sk_A @ sk_B)
% 1.18/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.18/1.39       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['101', '102'])).
% 1.18/1.39  thf('104', plain, ($false),
% 1.18/1.39      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '103'])).
% 1.18/1.39  
% 1.18/1.39  % SZS output end Refutation
% 1.18/1.39  
% 1.18/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
