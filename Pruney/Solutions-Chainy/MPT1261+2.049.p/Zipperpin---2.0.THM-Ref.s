%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dknkh5tJIB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 327 expanded)
%              Number of leaves         :   46 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          : 1452 (3344 expanded)
%              Number of equality atoms :  121 ( 266 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k6_subset_1 @ X34 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ ( k6_subset_1 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('20',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X51 @ X50 ) @ X50 )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ ( k6_subset_1 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40','41'])).

thf('43',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ ( k6_subset_1 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('45',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('71',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ ( k6_subset_1 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('73',plain,(
    ! [X25: $i,X26: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('81',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('91',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('97',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40','41'])).

thf('99',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('101',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k6_subset_1 @ X32 @ X33 )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k6_subset_1 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('105',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('110',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','108','111'])).

thf('113',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X44 @ X45 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('116',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','60','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dknkh5tJIB
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 1887 iterations in 0.525s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.76/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.99  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.99  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.76/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.76/0.99  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(t77_tops_1, conjecture,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99           ( ( v4_pre_topc @ B @ A ) <=>
% 0.76/0.99             ( ( k2_tops_1 @ A @ B ) =
% 0.76/0.99               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i]:
% 0.76/0.99        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99          ( ![B:$i]:
% 0.76/0.99            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99              ( ( v4_pre_topc @ B @ A ) <=>
% 0.76/0.99                ( ( k2_tops_1 @ A @ B ) =
% 0.76/0.99                  ( k7_subset_1 @
% 0.76/0.99                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99              (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      (~
% 0.76/0.99       (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.76/0.99       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('2', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t74_tops_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_pre_topc @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99           ( ( k1_tops_1 @ A @ B ) =
% 0.76/0.99             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X52 : $i, X53 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.76/0.99          | ((k1_tops_1 @ X53 @ X52)
% 0.76/0.99              = (k7_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 0.76/0.99                 (k2_tops_1 @ X53 @ X52)))
% 0.76/0.99          | ~ (l1_pre_topc @ X53))),
% 0.76/0.99      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.76/0.99  thf('4', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.99            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k7_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.99       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.76/0.99          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.76/0.99  thf(redefinition_k6_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('9', plain,
% 0.76/0.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.76/0.99          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k6_subset_1 @ X34 @ X36)))),
% 0.76/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.76/0.99  thf('10', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '9'])).
% 0.76/0.99  thf('11', plain,
% 0.76/0.99      (((k1_tops_1 @ sk_A @ sk_B)
% 0.76/0.99         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.76/0.99  thf(t48_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('12', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i]:
% 0.76/0.99         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.99           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X15 @ (k6_subset_1 @ X15 @ X16))
% 0.76/0.99           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.99      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.76/0.99  thf('16', plain,
% 0.76/0.99      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.76/0.99         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['11', '15'])).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.99        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('18', plain,
% 0.76/0.99      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('split', [status(esa)], ['17'])).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t69_tops_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_pre_topc @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99           ( ( v4_pre_topc @ B @ A ) =>
% 0.76/0.99             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      (![X50 : $i, X51 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.76/0.99          | (r1_tarski @ (k2_tops_1 @ X51 @ X50) @ X50)
% 0.76/0.99          | ~ (v4_pre_topc @ X50 @ X51)
% 0.76/0.99          | ~ (l1_pre_topc @ X51))),
% 0.76/0.99      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.76/0.99        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.76/0.99        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('24', plain,
% 0.76/0.99      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['18', '23'])).
% 0.76/0.99  thf(t28_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      (![X7 : $i, X8 : $i]:
% 0.76/0.99         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.76/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.99  thf('26', plain,
% 0.76/0.99      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.76/0.99          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.99  thf(t100_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.99  thf('27', plain,
% 0.76/0.99      (![X1 : $i, X2 : $i]:
% 0.76/0.99         ((k4_xboole_0 @ X1 @ X2)
% 0.76/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      (![X1 : $i, X2 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X1 @ X2)
% 0.76/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.76/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.76/0.99          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.99             (k2_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['26', '29'])).
% 0.76/0.99  thf(t3_boole, axiom,
% 0.76/0.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.99  thf('31', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.99  thf('32', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('33', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.76/0.99      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X15 @ (k6_subset_1 @ X15 @ X16))
% 0.76/0.99           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.99      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.76/0.99  thf('35', plain,
% 0.76/0.99      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.76/0.99  thf('36', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.76/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      (![X1 : $i, X2 : $i]:
% 0.76/0.99         ((k4_xboole_0 @ X1 @ X2)
% 0.76/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.99  thf('38', plain,
% 0.76/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['36', '37'])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.76/0.99      inference('demod', [status(thm)], ['38', '39'])).
% 0.76/0.99  thf(t2_boole, axiom,
% 0.76/0.99    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.99  thf('41', plain,
% 0.76/0.99      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.99  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['35', '40', '41'])).
% 0.76/0.99  thf('43', plain,
% 0.76/0.99      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['30', '42'])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X15 @ (k6_subset_1 @ X15 @ X16))
% 0.76/0.99           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.99      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.76/0.99          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['43', '44'])).
% 0.76/0.99  thf('46', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.76/0.99      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/0.99  thf('47', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf(commutativity_k2_tarski, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      (![X17 : $i, X18 : $i]:
% 0.76/0.99         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.99  thf(t12_setfam_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      (![X37 : $i, X38 : $i]:
% 0.76/0.99         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.76/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.99  thf('50', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['48', '49'])).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      (![X37 : $i, X38 : $i]:
% 0.76/0.99         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.76/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['50', '51'])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['47', '52'])).
% 0.76/0.99  thf('54', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['16', '53'])).
% 0.76/0.99  thf('55', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '9'])).
% 0.76/0.99  thf('56', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99              (k1_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('57', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.99  thf('58', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.76/0.99             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['54', '57'])).
% 0.76/0.99  thf('59', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.76/0.99       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('simplify', [status(thm)], ['58'])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.76/0.99       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('split', [status(esa)], ['17'])).
% 0.76/0.99  thf('61', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(dt_k2_tops_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.99       ( m1_subset_1 @
% 0.76/0.99         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.99  thf('62', plain,
% 0.76/0.99      (![X42 : $i, X43 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ X42)
% 0.76/0.99          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.76/0.99          | (m1_subset_1 @ (k2_tops_1 @ X42 @ X43) @ 
% 0.76/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X42))))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.76/0.99  thf('63', plain,
% 0.76/0.99      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.99  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('65', plain,
% 0.76/0.99      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.99  thf(t3_subset, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.99  thf('66', plain,
% 0.76/0.99      (![X39 : $i, X40 : $i]:
% 0.76/0.99         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.99  thf('67', plain,
% 0.76/0.99      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['65', '66'])).
% 0.76/0.99  thf('68', plain,
% 0.76/0.99      (![X7 : $i, X8 : $i]:
% 0.76/0.99         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.76/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.99  thf('69', plain,
% 0.76/0.99      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.99         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.99  thf('70', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['50', '51'])).
% 0.76/0.99  thf('71', plain,
% 0.76/0.99      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.99         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['69', '70'])).
% 0.76/0.99  thf('72', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X15 @ (k6_subset_1 @ X15 @ X16))
% 0.76/0.99           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.99      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.76/0.99  thf(dt_k6_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.99  thf('73', plain,
% 0.76/0.99      (![X25 : $i, X26 : $i]:
% 0.76/0.99         (m1_subset_1 @ (k6_subset_1 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.76/0.99  thf('74', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['72', '73'])).
% 0.76/0.99  thf('75', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k4_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.99       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.99  thf('76', plain,
% 0.76/0.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.76/0.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 0.76/0.99          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.76/0.99  thf('77', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.99            = (k2_xboole_0 @ sk_B @ X0))
% 0.76/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['75', '76'])).
% 0.76/0.99  thf('78', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.99           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['74', '77'])).
% 0.76/0.99  thf('79', plain,
% 0.76/0.99      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.99         = (k2_xboole_0 @ sk_B @ 
% 0.76/0.99            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['71', '78'])).
% 0.76/0.99  thf('80', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t65_tops_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_pre_topc @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99           ( ( k2_pre_topc @ A @ B ) =
% 0.76/0.99             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.99  thf('81', plain,
% 0.76/0.99      (![X48 : $i, X49 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.76/0.99          | ((k2_pre_topc @ X49 @ X48)
% 0.76/0.99              = (k4_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.76/0.99                 (k2_tops_1 @ X49 @ X48)))
% 0.76/0.99          | ~ (l1_pre_topc @ X49))),
% 0.76/0.99      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.76/0.99  thf('82', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.76/0.99            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.76/0.99  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('84', plain,
% 0.76/0.99      (((k2_pre_topc @ sk_A @ sk_B)
% 0.76/0.99         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.76/0.99  thf('85', plain,
% 0.76/0.99      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.99         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['69', '70'])).
% 0.76/0.99  thf('86', plain,
% 0.76/0.99      (((k2_pre_topc @ sk_A @ sk_B)
% 0.76/0.99         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('demod', [status(thm)], ['79', '84', '85'])).
% 0.76/0.99  thf('87', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.99           = (k6_subset_1 @ sk_B @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '9'])).
% 0.76/0.99  thf('88', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('split', [status(esa)], ['17'])).
% 0.76/0.99  thf('89', plain,
% 0.76/0.99      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['87', '88'])).
% 0.76/0.99  thf(t36_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.99  thf('90', plain,
% 0.76/0.99      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.76/0.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.99  thf('91', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('92', plain,
% 0.76/0.99      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.76/0.99      inference('demod', [status(thm)], ['90', '91'])).
% 0.76/0.99  thf('93', plain,
% 0.76/0.99      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['89', '92'])).
% 0.76/0.99  thf('94', plain,
% 0.76/0.99      (![X7 : $i, X8 : $i]:
% 0.76/0.99         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.76/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.99  thf('95', plain,
% 0.76/0.99      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.76/0.99          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['93', '94'])).
% 0.76/0.99  thf('96', plain,
% 0.76/0.99      (![X1 : $i, X2 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X1 @ X2)
% 0.76/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.76/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.99  thf('97', plain,
% 0.76/0.99      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.76/0.99          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.99             (k2_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['95', '96'])).
% 0.76/0.99  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['35', '40', '41'])).
% 0.76/0.99  thf('99', plain,
% 0.76/0.99      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.76/0.99  thf(t39_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('100', plain,
% 0.76/0.99      (![X12 : $i, X13 : $i]:
% 0.76/0.99         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.76/0.99           = (k2_xboole_0 @ X12 @ X13))),
% 0.76/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.99  thf('101', plain,
% 0.76/0.99      (![X32 : $i, X33 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('102', plain,
% 0.76/0.99      (![X12 : $i, X13 : $i]:
% 0.76/0.99         ((k2_xboole_0 @ X12 @ (k6_subset_1 @ X13 @ X12))
% 0.76/0.99           = (k2_xboole_0 @ X12 @ X13))),
% 0.76/0.99      inference('demod', [status(thm)], ['100', '101'])).
% 0.76/0.99  thf('103', plain,
% 0.76/0.99      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.76/0.99          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '102'])).
% 0.76/0.99  thf('104', plain,
% 0.76/0.99      (![X17 : $i, X18 : $i]:
% 0.76/0.99         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.99  thf(l51_zfmisc_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('105', plain,
% 0.76/0.99      (![X19 : $i, X20 : $i]:
% 0.76/0.99         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.76/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.76/0.99  thf('106', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['104', '105'])).
% 0.76/0.99  thf('107', plain,
% 0.76/0.99      (![X19 : $i, X20 : $i]:
% 0.76/0.99         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.76/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.76/0.99  thf('108', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['106', '107'])).
% 0.76/0.99  thf('109', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['106', '107'])).
% 0.76/0.99  thf(t1_boole, axiom,
% 0.76/0.99    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.99  thf('110', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [t1_boole])).
% 0.76/0.99  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['109', '110'])).
% 0.76/0.99  thf('112', plain,
% 0.76/0.99      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('demod', [status(thm)], ['103', '108', '111'])).
% 0.76/0.99  thf('113', plain,
% 0.76/0.99      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['86', '112'])).
% 0.76/0.99  thf('114', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(fc1_tops_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.76/0.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.99       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.76/0.99  thf('115', plain,
% 0.76/0.99      (![X44 : $i, X45 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ X44)
% 0.76/0.99          | ~ (v2_pre_topc @ X44)
% 0.76/0.99          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.76/0.99          | (v4_pre_topc @ (k2_pre_topc @ X44 @ X45) @ X44))),
% 0.76/0.99      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.76/0.99  thf('116', plain,
% 0.76/0.99      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.76/0.99        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['114', '115'])).
% 0.76/0.99  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('119', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.76/0.99      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.76/0.99  thf('120', plain,
% 0.76/0.99      (((v4_pre_topc @ sk_B @ sk_A))
% 0.76/0.99         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.76/0.99      inference('sup+', [status(thm)], ['113', '119'])).
% 0.76/0.99  thf('121', plain,
% 0.76/0.99      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('122', plain,
% 0.76/0.99      (~
% 0.76/0.99       (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.99          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.99             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.76/0.99       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['120', '121'])).
% 0.76/0.99  thf('123', plain, ($false),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['1', '59', '60', '122'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.86/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
