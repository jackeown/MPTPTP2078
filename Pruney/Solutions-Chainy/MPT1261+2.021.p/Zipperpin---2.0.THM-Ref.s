%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tk3JkZQWlL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:39 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 380 expanded)
%              Number of leaves         :   51 ( 137 expanded)
%              Depth                    :   22
%              Number of atoms          : 1725 (3785 expanded)
%              Number of equality atoms :  139 ( 302 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v4_pre_topc @ X56 @ X57 )
      | ( ( k2_pre_topc @ X57 @ X56 )
        = X56 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
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
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k2_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ ( k2_pre_topc @ X63 @ X62 ) @ ( k1_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ( ( k7_subset_1 @ X52 @ X51 @ X53 )
        = ( k4_xboole_0 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ( ( k7_subset_1 @ X52 @ X51 @ X53 )
        = ( k6_subset_1 @ X51 @ X53 ) ) ) ),
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
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X15 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('49',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ ( k6_subset_1 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('53',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('57',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( r2_hidden @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('66',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X21: $i] :
      ( ( k6_subset_1 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ ( k6_subset_1 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('77',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','74','79'])).

thf('81',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','80'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('83',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('84',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['54','91'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('93',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('94',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('95',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('96',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('101',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ ( k6_subset_1 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('102',plain,(
    ! [X39: $i,X40: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('107',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k4_subset_1 @ X47 @ X46 @ X48 )
        = ( k2_xboole_0 @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('108',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('109',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k4_subset_1 @ X47 @ X46 @ X48 )
        = ( k3_tarski @ ( k2_tarski @ X46 @ X48 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X15 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('122',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('123',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('124',plain,(
    ! [X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ k1_xboole_0 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','125'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('127',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('128',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('129',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('130',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('131',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ ( k6_subset_1 @ X20 @ X19 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ k1_xboole_0 ) )
      = ( k3_tarski @ ( k2_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['126','131'])).

thf('133',plain,(
    ! [X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ k1_xboole_0 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_tarski @ ( k2_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['111','134'])).

thf('136',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('138',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k2_pre_topc @ X67 @ X66 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('139',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('144',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X60 @ X61 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('145',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['142','148'])).

thf('150',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tk3JkZQWlL
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.19/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.38  % Solved by: fo/fo7.sh
% 1.19/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.38  % done 3270 iterations in 0.932s
% 1.19/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.38  % SZS output start Refutation
% 1.19/1.38  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.38  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.19/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.38  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.19/1.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.38  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.19/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.19/1.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.38  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.19/1.38  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.38  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.19/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.38  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.19/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.19/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.19/1.38  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.19/1.38  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(t77_tops_1, conjecture,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.38           ( ( v4_pre_topc @ B @ A ) <=>
% 1.19/1.38             ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.38               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.38    (~( ![A:$i]:
% 1.19/1.38        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.38          ( ![B:$i]:
% 1.19/1.38            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.38              ( ( v4_pre_topc @ B @ A ) <=>
% 1.19/1.38                ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.38                  ( k7_subset_1 @
% 1.19/1.38                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.19/1.38    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.19/1.38  thf('0', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38              (k1_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('1', plain,
% 1.19/1.38      (~
% 1.19/1.38       (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.38       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('split', [status(esa)], ['0'])).
% 1.19/1.38  thf('2', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('3', plain,
% 1.19/1.38      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.38      inference('split', [status(esa)], ['2'])).
% 1.19/1.38  thf('4', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf(t52_pre_topc, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( l1_pre_topc @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.38           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.19/1.38             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.19/1.38               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.19/1.38  thf('5', plain,
% 1.19/1.38      (![X56 : $i, X57 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.19/1.38          | ~ (v4_pre_topc @ X56 @ X57)
% 1.19/1.38          | ((k2_pre_topc @ X57 @ X56) = (X56))
% 1.19/1.38          | ~ (l1_pre_topc @ X57))),
% 1.19/1.38      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.19/1.38  thf('6', plain,
% 1.19/1.38      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.38        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.19/1.38        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('sup-', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('8', plain,
% 1.19/1.38      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('demod', [status(thm)], ['6', '7'])).
% 1.19/1.38  thf('9', plain,
% 1.19/1.38      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.19/1.38         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['3', '8'])).
% 1.19/1.38  thf('10', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf(l78_tops_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( l1_pre_topc @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.38           ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.38             ( k7_subset_1 @
% 1.19/1.38               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.19/1.38               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.19/1.38  thf('11', plain,
% 1.19/1.38      (![X62 : $i, X63 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 1.19/1.38          | ((k2_tops_1 @ X63 @ X62)
% 1.19/1.38              = (k7_subset_1 @ (u1_struct_0 @ X63) @ 
% 1.19/1.38                 (k2_pre_topc @ X63 @ X62) @ (k1_tops_1 @ X63 @ X62)))
% 1.19/1.38          | ~ (l1_pre_topc @ X63))),
% 1.19/1.38      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.19/1.38  thf('12', plain,
% 1.19/1.38      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.38        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.38               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['10', '11'])).
% 1.19/1.38  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('14', plain,
% 1.19/1.38      (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.19/1.38            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('15', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.38      inference('sup+', [status(thm)], ['9', '14'])).
% 1.19/1.38  thf('16', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf(redefinition_k7_subset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.38       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.19/1.38  thf('17', plain,
% 1.19/1.38      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 1.19/1.38          | ((k7_subset_1 @ X52 @ X51 @ X53) = (k4_xboole_0 @ X51 @ X53)))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.19/1.38  thf(redefinition_k6_subset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.19/1.38  thf('18', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('19', plain,
% 1.19/1.38      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 1.19/1.38          | ((k7_subset_1 @ X52 @ X51 @ X53) = (k6_subset_1 @ X51 @ X53)))),
% 1.19/1.38      inference('demod', [status(thm)], ['17', '18'])).
% 1.19/1.38  thf('20', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.38           = (k6_subset_1 @ sk_B @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['16', '19'])).
% 1.19/1.38  thf('21', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '20'])).
% 1.19/1.38  thf('22', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.38           = (k6_subset_1 @ sk_B @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['16', '19'])).
% 1.19/1.38  thf('23', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38              (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= (~
% 1.19/1.38             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('split', [status(esa)], ['0'])).
% 1.19/1.38  thf('24', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= (~
% 1.19/1.38             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['22', '23'])).
% 1.19/1.38  thf('25', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38         <= (~
% 1.19/1.38             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.19/1.38             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['21', '24'])).
% 1.19/1.38  thf('26', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.38       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('simplify', [status(thm)], ['25'])).
% 1.19/1.38  thf('27', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.38       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.38      inference('split', [status(esa)], ['2'])).
% 1.19/1.38  thf('28', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.38           = (k6_subset_1 @ sk_B @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['16', '19'])).
% 1.19/1.38  thf('29', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('split', [status(esa)], ['2'])).
% 1.19/1.38  thf('30', plain,
% 1.19/1.38      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['28', '29'])).
% 1.19/1.38  thf(t36_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.38  thf('31', plain,
% 1.19/1.38      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 1.19/1.38      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.38  thf('32', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('33', plain,
% 1.19/1.38      (![X15 : $i, X16 : $i]: (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X15)),
% 1.19/1.38      inference('demod', [status(thm)], ['31', '32'])).
% 1.19/1.38  thf('34', plain,
% 1.19/1.38      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['30', '33'])).
% 1.19/1.38  thf(t28_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.19/1.38  thf('35', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i]:
% 1.19/1.38         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.19/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.38  thf('36', plain,
% 1.19/1.38      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.19/1.38          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['34', '35'])).
% 1.19/1.38  thf(commutativity_k2_tarski, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.19/1.38  thf('37', plain,
% 1.19/1.38      (![X31 : $i, X32 : $i]:
% 1.19/1.38         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 1.19/1.38      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.38  thf(t12_setfam_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.19/1.38  thf('38', plain,
% 1.19/1.38      (![X54 : $i, X55 : $i]:
% 1.19/1.38         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.19/1.38      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.19/1.38  thf('39', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['37', '38'])).
% 1.19/1.38  thf('40', plain,
% 1.19/1.38      (![X54 : $i, X55 : $i]:
% 1.19/1.38         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.19/1.38      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.19/1.38  thf('41', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['39', '40'])).
% 1.19/1.38  thf('42', plain,
% 1.19/1.38      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.38          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('demod', [status(thm)], ['36', '41'])).
% 1.19/1.38  thf(t100_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.38  thf('43', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]:
% 1.19/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.19/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.38  thf('44', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('45', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X5 @ X6)
% 1.19/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.19/1.38      inference('demod', [status(thm)], ['43', '44'])).
% 1.19/1.38  thf('46', plain,
% 1.19/1.38      ((((k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.38          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['42', '45'])).
% 1.19/1.38  thf(t48_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.19/1.38  thf('47', plain,
% 1.19/1.38      (![X29 : $i, X30 : $i]:
% 1.19/1.38         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 1.19/1.38           = (k3_xboole_0 @ X29 @ X30))),
% 1.19/1.38      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.19/1.38  thf('48', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('49', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('50', plain,
% 1.19/1.38      (![X29 : $i, X30 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X29 @ (k6_subset_1 @ X29 @ X30))
% 1.19/1.38           = (k3_xboole_0 @ X29 @ X30))),
% 1.19/1.38      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.19/1.38  thf('51', plain,
% 1.19/1.38      ((((k6_subset_1 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['46', '50'])).
% 1.19/1.38  thf('52', plain,
% 1.19/1.38      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.38          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('demod', [status(thm)], ['36', '41'])).
% 1.19/1.38  thf('53', plain,
% 1.19/1.38      ((((k6_subset_1 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.38         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.38                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.38                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.38      inference('demod', [status(thm)], ['51', '52'])).
% 1.19/1.38  thf('54', plain,
% 1.19/1.38      (![X31 : $i, X32 : $i]:
% 1.19/1.38         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 1.19/1.38      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.38  thf(d3_tarski, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ B ) <=>
% 1.19/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.19/1.38  thf('55', plain,
% 1.19/1.38      (![X1 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf('56', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf(l3_subset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.19/1.38  thf('57', plain,
% 1.19/1.38      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.19/1.38         (~ (r2_hidden @ X43 @ X44)
% 1.19/1.38          | (r2_hidden @ X43 @ X45)
% 1.19/1.38          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.19/1.38      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.19/1.38  thf('58', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.38  thf('59', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((r1_tarski @ sk_B @ X0)
% 1.19/1.38          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['55', '58'])).
% 1.19/1.38  thf('60', plain,
% 1.19/1.38      (![X1 : $i, X3 : $i]:
% 1.19/1.38         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.19/1.38  thf('61', plain,
% 1.19/1.38      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 1.19/1.38        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['59', '60'])).
% 1.19/1.38  thf('62', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.19/1.38      inference('simplify', [status(thm)], ['61'])).
% 1.19/1.38  thf('63', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i]:
% 1.19/1.38         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.19/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.38  thf('64', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['62', '63'])).
% 1.19/1.38  thf('65', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X5 @ X6)
% 1.19/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.19/1.38      inference('demod', [status(thm)], ['43', '44'])).
% 1.19/1.38  thf('66', plain,
% 1.19/1.38      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.19/1.38         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.19/1.38      inference('sup+', [status(thm)], ['64', '65'])).
% 1.19/1.38  thf(t3_boole, axiom,
% 1.19/1.38    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.19/1.38  thf('67', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_boole])).
% 1.19/1.38  thf('68', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('69', plain, (![X21 : $i]: ((k6_subset_1 @ X21 @ k1_xboole_0) = (X21))),
% 1.19/1.38      inference('demod', [status(thm)], ['67', '68'])).
% 1.19/1.38  thf('70', plain,
% 1.19/1.38      (![X29 : $i, X30 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X29 @ (k6_subset_1 @ X29 @ X30))
% 1.19/1.38           = (k3_xboole_0 @ X29 @ X30))),
% 1.19/1.38      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.19/1.38  thf('71', plain,
% 1.19/1.38      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['69', '70'])).
% 1.19/1.38  thf(idempotence_k3_xboole_0, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.19/1.38  thf('72', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.19/1.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.19/1.38  thf('73', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X5 @ X6)
% 1.19/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.19/1.38      inference('demod', [status(thm)], ['43', '44'])).
% 1.19/1.38  thf('74', plain,
% 1.19/1.38      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['72', '73'])).
% 1.19/1.38  thf('75', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['39', '40'])).
% 1.19/1.38  thf(t17_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.38  thf('76', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.19/1.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.38  thf(t3_xboole_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.19/1.38  thf('77', plain,
% 1.19/1.38      (![X22 : $i]:
% 1.19/1.38         (((X22) = (k1_xboole_0)) | ~ (r1_tarski @ X22 @ k1_xboole_0))),
% 1.19/1.38      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.19/1.38  thf('78', plain,
% 1.19/1.38      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['76', '77'])).
% 1.19/1.38  thf('79', plain,
% 1.19/1.38      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['75', '78'])).
% 1.19/1.38  thf('80', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.19/1.38      inference('demod', [status(thm)], ['71', '74', '79'])).
% 1.19/1.38  thf('81', plain,
% 1.19/1.38      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.19/1.38      inference('demod', [status(thm)], ['66', '80'])).
% 1.19/1.38  thf(t44_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.19/1.38       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.19/1.38  thf('82', plain,
% 1.19/1.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.38         ((r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 1.19/1.38          | ~ (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X28))),
% 1.19/1.38      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.19/1.38  thf('83', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('84', plain,
% 1.19/1.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.38         ((r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 1.19/1.38          | ~ (r1_tarski @ (k6_subset_1 @ X26 @ X27) @ X28))),
% 1.19/1.38      inference('demod', [status(thm)], ['82', '83'])).
% 1.19/1.38  thf(l51_zfmisc_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.38  thf('85', plain,
% 1.19/1.38      (![X33 : $i, X34 : $i]:
% 1.19/1.38         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.38      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.38  thf('86', plain,
% 1.19/1.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.38         ((r1_tarski @ X26 @ (k3_tarski @ (k2_tarski @ X27 @ X28)))
% 1.19/1.38          | ~ (r1_tarski @ (k6_subset_1 @ X26 @ X27) @ X28))),
% 1.19/1.38      inference('demod', [status(thm)], ['84', '85'])).
% 1.19/1.38  thf('87', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.19/1.38          | (r1_tarski @ sk_B @ 
% 1.19/1.38             (k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ X0))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['81', '86'])).
% 1.19/1.38  thf('88', plain,
% 1.19/1.38      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['75', '78'])).
% 1.19/1.38  thf('89', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.19/1.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.38  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.19/1.38      inference('sup+', [status(thm)], ['88', '89'])).
% 1.19/1.38  thf('91', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (r1_tarski @ sk_B @ 
% 1.19/1.38          (k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.19/1.38      inference('demod', [status(thm)], ['87', '90'])).
% 1.19/1.38  thf('92', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (r1_tarski @ sk_B @ 
% 1.19/1.38          (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))),
% 1.19/1.38      inference('sup+', [status(thm)], ['54', '91'])).
% 1.19/1.38  thf(t43_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.19/1.38       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.19/1.38  thf('93', plain,
% 1.19/1.38      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.19/1.38         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.19/1.38          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.19/1.38  thf('94', plain,
% 1.19/1.38      (![X49 : $i, X50 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.38  thf('95', plain,
% 1.19/1.38      (![X33 : $i, X34 : $i]:
% 1.19/1.38         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.38      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.38  thf('96', plain,
% 1.19/1.38      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.19/1.38         ((r1_tarski @ (k6_subset_1 @ X23 @ X24) @ X25)
% 1.19/1.38          | ~ (r1_tarski @ X23 @ (k3_tarski @ (k2_tarski @ X24 @ X25))))),
% 1.19/1.38      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.19/1.38  thf('97', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.19/1.38      inference('sup-', [status(thm)], ['92', '96'])).
% 1.19/1.38  thf('98', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i]:
% 1.19/1.38         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.19/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.38  thf('99', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((k3_xboole_0 @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))
% 1.19/1.38           = (k6_subset_1 @ sk_B @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['97', '98'])).
% 1.19/1.38  thf('100', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['39', '40'])).
% 1.19/1.38  thf('101', plain,
% 1.19/1.38      (![X29 : $i, X30 : $i]:
% 1.19/1.38         ((k6_subset_1 @ X29 @ (k6_subset_1 @ X29 @ X30))
% 1.19/1.38           = (k3_xboole_0 @ X29 @ X30))),
% 1.19/1.38      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.19/1.38  thf(dt_k6_subset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.19/1.38  thf('102', plain,
% 1.19/1.38      (![X39 : $i, X40 : $i]:
% 1.19/1.38         (m1_subset_1 @ (k6_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.19/1.38  thf('103', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.19/1.38      inference('sup+', [status(thm)], ['101', '102'])).
% 1.19/1.38  thf('104', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['100', '103'])).
% 1.19/1.38  thf('105', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 1.19/1.38          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('sup+', [status(thm)], ['99', '104'])).
% 1.19/1.38  thf('106', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf(redefinition_k4_subset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.19/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.19/1.38       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.19/1.38  thf('107', plain,
% 1.19/1.38      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 1.19/1.38          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47))
% 1.19/1.38          | ((k4_subset_1 @ X47 @ X46 @ X48) = (k2_xboole_0 @ X46 @ X48)))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.19/1.39  thf('108', plain,
% 1.19/1.39      (![X33 : $i, X34 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('109', plain,
% 1.19/1.39      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 1.19/1.39          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47))
% 1.19/1.39          | ((k4_subset_1 @ X47 @ X46 @ X48)
% 1.19/1.39              = (k3_tarski @ (k2_tarski @ X46 @ X48))))),
% 1.19/1.39      inference('demod', [status(thm)], ['107', '108'])).
% 1.19/1.39  thf('110', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.39            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['106', '109'])).
% 1.19/1.39  thf('111', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39           (k6_subset_1 @ sk_B @ X0))
% 1.19/1.39           = (k3_tarski @ (k2_tarski @ sk_B @ (k6_subset_1 @ sk_B @ X0))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['105', '110'])).
% 1.19/1.39  thf('112', plain,
% 1.19/1.39      (![X15 : $i, X16 : $i]: (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X15)),
% 1.19/1.39      inference('demod', [status(thm)], ['31', '32'])).
% 1.19/1.39  thf('113', plain,
% 1.19/1.39      (![X13 : $i, X14 : $i]:
% 1.19/1.39         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.19/1.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.39  thf('114', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k3_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0)
% 1.19/1.39           = (k6_subset_1 @ X0 @ X1))),
% 1.19/1.39      inference('sup-', [status(thm)], ['112', '113'])).
% 1.19/1.39  thf('115', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['39', '40'])).
% 1.19/1.39  thf('116', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.19/1.39           = (k6_subset_1 @ X0 @ X1))),
% 1.19/1.39      inference('demod', [status(thm)], ['114', '115'])).
% 1.19/1.39  thf('117', plain,
% 1.19/1.39      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.19/1.39      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.39  thf('118', plain,
% 1.19/1.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.19/1.39         ((r1_tarski @ (k6_subset_1 @ X23 @ X24) @ X25)
% 1.19/1.39          | ~ (r1_tarski @ X23 @ (k3_tarski @ (k2_tarski @ X24 @ X25))))),
% 1.19/1.39      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.19/1.39  thf('119', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         (r1_tarski @ 
% 1.19/1.39          (k6_subset_1 @ 
% 1.19/1.39           (k3_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 1.19/1.39          X0)),
% 1.19/1.39      inference('sup-', [status(thm)], ['117', '118'])).
% 1.19/1.39  thf('120', plain,
% 1.19/1.39      (![X22 : $i]:
% 1.19/1.39         (((X22) = (k1_xboole_0)) | ~ (r1_tarski @ X22 @ k1_xboole_0))),
% 1.19/1.39      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.19/1.39  thf('121', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k6_subset_1 @ 
% 1.19/1.39           (k3_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1) @ 
% 1.19/1.39           X0) = (k1_xboole_0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['119', '120'])).
% 1.19/1.39  thf(t1_boole, axiom,
% 1.19/1.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.19/1.39  thf('122', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.19/1.39      inference('cnf', [status(esa)], [t1_boole])).
% 1.19/1.39  thf('123', plain,
% 1.19/1.39      (![X33 : $i, X34 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('124', plain,
% 1.19/1.39      (![X9 : $i]: ((k3_tarski @ (k2_tarski @ X9 @ k1_xboole_0)) = (X9))),
% 1.19/1.39      inference('demod', [status(thm)], ['122', '123'])).
% 1.19/1.39  thf('125', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k6_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.19/1.39      inference('demod', [status(thm)], ['121', '124'])).
% 1.19/1.39  thf('126', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.19/1.39      inference('sup+', [status(thm)], ['116', '125'])).
% 1.19/1.39  thf(t39_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('127', plain,
% 1.19/1.39      (![X19 : $i, X20 : $i]:
% 1.19/1.39         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 1.19/1.39           = (k2_xboole_0 @ X19 @ X20))),
% 1.19/1.39      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.19/1.39  thf('128', plain,
% 1.19/1.39      (![X49 : $i, X50 : $i]:
% 1.19/1.39         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.19/1.39  thf('129', plain,
% 1.19/1.39      (![X33 : $i, X34 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('130', plain,
% 1.19/1.39      (![X33 : $i, X34 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('131', plain,
% 1.19/1.39      (![X19 : $i, X20 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X19 @ (k6_subset_1 @ X20 @ X19)))
% 1.19/1.39           = (k3_tarski @ (k2_tarski @ X19 @ X20)))),
% 1.19/1.39      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 1.19/1.39  thf('132', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X1 @ k1_xboole_0))
% 1.19/1.39           = (k3_tarski @ (k2_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['126', '131'])).
% 1.19/1.39  thf('133', plain,
% 1.19/1.39      (![X9 : $i]: ((k3_tarski @ (k2_tarski @ X9 @ k1_xboole_0)) = (X9))),
% 1.19/1.39      inference('demod', [status(thm)], ['122', '123'])).
% 1.19/1.39  thf('134', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((X1) = (k3_tarski @ (k2_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))))),
% 1.19/1.39      inference('demod', [status(thm)], ['132', '133'])).
% 1.19/1.39  thf('135', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39           (k6_subset_1 @ sk_B @ X0)) = (sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['111', '134'])).
% 1.19/1.39  thf('136', plain,
% 1.19/1.39      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.39          = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['53', '135'])).
% 1.19/1.39  thf('137', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t65_tops_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( l1_pre_topc @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( ( k2_pre_topc @ A @ B ) =
% 1.19/1.39             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.19/1.39  thf('138', plain,
% 1.19/1.39      (![X66 : $i, X67 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 1.19/1.39          | ((k2_pre_topc @ X67 @ X66)
% 1.19/1.39              = (k4_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 1.19/1.39                 (k2_tops_1 @ X67 @ X66)))
% 1.19/1.39          | ~ (l1_pre_topc @ X67))),
% 1.19/1.39      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.19/1.39  thf('139', plain,
% 1.19/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.39        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['137', '138'])).
% 1.19/1.39  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('141', plain,
% 1.19/1.39      (((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('demod', [status(thm)], ['139', '140'])).
% 1.19/1.39  thf('142', plain,
% 1.19/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['136', '141'])).
% 1.19/1.39  thf('143', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(fc1_tops_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.19/1.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.39       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.19/1.39  thf('144', plain,
% 1.19/1.39      (![X60 : $i, X61 : $i]:
% 1.19/1.39         (~ (l1_pre_topc @ X60)
% 1.19/1.39          | ~ (v2_pre_topc @ X60)
% 1.19/1.39          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.19/1.39          | (v4_pre_topc @ (k2_pre_topc @ X60 @ X61) @ X60))),
% 1.19/1.39      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.19/1.39  thf('145', plain,
% 1.19/1.39      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.19/1.39        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['143', '144'])).
% 1.19/1.39  thf('146', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('148', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.19/1.39      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.19/1.39  thf('149', plain,
% 1.19/1.39      (((v4_pre_topc @ sk_B @ sk_A))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['142', '148'])).
% 1.19/1.39  thf('150', plain,
% 1.19/1.39      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('split', [status(esa)], ['0'])).
% 1.19/1.39  thf('151', plain,
% 1.19/1.39      (~
% 1.19/1.39       (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.39       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['149', '150'])).
% 1.19/1.39  thf('152', plain, ($false),
% 1.19/1.39      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '151'])).
% 1.19/1.39  
% 1.19/1.39  % SZS output end Refutation
% 1.19/1.39  
% 1.19/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
