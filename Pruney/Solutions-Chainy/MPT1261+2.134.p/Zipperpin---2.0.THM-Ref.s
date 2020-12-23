%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al03fxB60w

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 486 expanded)
%              Number of leaves         :   41 ( 162 expanded)
%              Depth                    :   24
%              Number of atoms          : 1550 (4859 expanded)
%              Number of equality atoms :  129 ( 360 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('40',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( v4_pre_topc @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('96',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('102',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','103'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('112',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','118'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('120',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['79','123'])).

thf('125',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','124'])).

thf('126',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','125'])).

thf('127',plain,(
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

thf('128',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_pre_topc @ X38 )
      | ( ( k2_pre_topc @ X38 @ X37 )
       != X37 )
      | ( v4_pre_topc @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('136',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('138',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['50','136','137'])).

thf('139',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','138'])).

thf('140',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','139'])).

thf('141',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('143',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['50','136'])).

thf('145',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['140','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al03fxB60w
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 2309 iterations in 0.713s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.17  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.99/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.17  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.99/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.17  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.99/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.17  thf(t77_tops_1, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.17             ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17          ( ![B:$i]:
% 0.99/1.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17              ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.17                ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17                  ( k7_subset_1 @
% 0.99/1.17                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t74_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k1_tops_1 @ A @ B ) =
% 0.99/1.17             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      (![X45 : $i, X46 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.99/1.17          | ((k1_tops_1 @ X46 @ X45)
% 0.99/1.17              = (k7_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.99/1.17                 (k2_tops_1 @ X46 @ X45)))
% 0.99/1.17          | ~ (l1_pre_topc @ X46))),
% 0.99/1.17      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k7_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.99/1.17          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.99/1.17  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf(t48_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf(t36_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf(t28_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.99/1.17           = (k4_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['12', '13'])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.99/1.17           = (k4_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('demod', [status(thm)], ['14', '15'])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k4_xboole_0 @ X1 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['11', '16'])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k4_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['8', '17'])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf(t3_subset, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X34 : $i, X36 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['23', '24'])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['22', '25'])).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['21', '26'])).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i]:
% 0.99/1.17         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.99/1.17      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.99/1.17           = (k3_xboole_0 @ X1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k3_xboole_0 @ X1 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['31', '32'])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.99/1.17           = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('demod', [status(thm)], ['20', '33'])).
% 0.99/1.17  thf('35', plain,
% 0.99/1.17      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.17      inference('sup+', [status(thm)], ['7', '34'])).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('split', [status(esa)], ['37'])).
% 0.99/1.17  thf('39', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t69_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( v4_pre_topc @ B @ A ) =>
% 0.99/1.17             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.99/1.17  thf('40', plain,
% 0.99/1.17      (![X43 : $i, X44 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.99/1.17          | (r1_tarski @ (k2_tops_1 @ X44 @ X43) @ X43)
% 0.99/1.17          | ~ (v4_pre_topc @ X43 @ X44)
% 0.99/1.17          | ~ (l1_pre_topc @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['39', '40'])).
% 0.99/1.17  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.17        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['41', '42'])).
% 0.99/1.17  thf('44', plain,
% 0.99/1.17      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.99/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['38', '43'])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('46', plain,
% 0.99/1.17      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['44', '45'])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['46', '47'])).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17              (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      (~
% 0.99/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.17       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('split', [status(esa)], ['49'])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t65_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k2_pre_topc @ A @ B ) =
% 0.99/1.17             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('52', plain,
% 0.99/1.17      (![X41 : $i, X42 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.99/1.17          | ((k2_pre_topc @ X42 @ X41)
% 0.99/1.17              = (k4_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.99/1.17                 (k2_tops_1 @ X42 @ X41)))
% 0.99/1.17          | ~ (l1_pre_topc @ X42))),
% 0.99/1.17      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.99/1.17  thf('53', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.17            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['51', '52'])).
% 0.99/1.17  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      (((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.17         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['53', '54'])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('split', [status(esa)], ['37'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['56', '57'])).
% 0.99/1.17  thf('59', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf('60', plain,
% 0.99/1.17      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['58', '59'])).
% 0.99/1.17  thf('61', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('62', plain,
% 0.99/1.17      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.99/1.17  thf('63', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('64', plain,
% 0.99/1.17      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('demod', [status(thm)], ['62', '63'])).
% 0.99/1.17  thf('65', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('66', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('67', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i]:
% 0.99/1.17         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('68', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['66', '67'])).
% 0.99/1.17  thf('69', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf(t1_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.99/1.17       ( r1_tarski @ A @ C ) ))).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.17         (~ (r1_tarski @ X10 @ X11)
% 0.99/1.17          | ~ (r1_tarski @ X11 @ X12)
% 0.99/1.17          | (r1_tarski @ X10 @ X12))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.99/1.17  thf('71', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.17      inference('sup-', [status(thm)], ['69', '70'])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['68', '71'])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (![X34 : $i, X36 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('74', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['72', '73'])).
% 0.99/1.17  thf('75', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['65', '74'])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k4_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.99/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.99/1.17       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.17  thf('77', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.99/1.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 0.99/1.17          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.99/1.17  thf('78', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17            = (k2_xboole_0 @ sk_B @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['76', '77'])).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17           (k3_xboole_0 @ sk_B @ X0))
% 0.99/1.17           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['75', '78'])).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.99/1.17           = (k4_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('demod', [status(thm)], ['14', '15'])).
% 0.99/1.17  thf('82', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf(t100_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('83', plain,
% 0.99/1.17      (![X5 : $i, X6 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X5 @ X6)
% 0.99/1.17           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('84', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X0 @ X1)
% 0.99/1.17           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['82', '83'])).
% 0.99/1.17  thf('85', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.99/1.17           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['81', '84'])).
% 0.99/1.17  thf('86', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.99/1.17           = (k3_xboole_0 @ X20 @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.17  thf('87', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.17      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.17  thf(t12_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.99/1.17  thf('88', plain,
% 0.99/1.17      (![X7 : $i, X8 : $i]:
% 0.99/1.17         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.99/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.17  thf('89', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['87', '88'])).
% 0.99/1.17  thf(t1_boole, axiom,
% 0.99/1.17    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.17  thf('90', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.17  thf('91', plain,
% 0.99/1.17      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['89', '90'])).
% 0.99/1.17  thf('92', plain,
% 0.99/1.17      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['86', '91'])).
% 0.99/1.17  thf('93', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.17  thf('94', plain,
% 0.99/1.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['92', '93'])).
% 0.99/1.17  thf('95', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.99/1.17      inference('sup+', [status(thm)], ['22', '25'])).
% 0.99/1.17  thf('96', plain,
% 0.99/1.17      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['94', '95'])).
% 0.99/1.17  thf(involutiveness_k3_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.99/1.17  thf('97', plain,
% 0.99/1.17      (![X26 : $i, X27 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 0.99/1.17          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.99/1.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.99/1.17  thf('98', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['96', '97'])).
% 0.99/1.17  thf('99', plain,
% 0.99/1.17      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['94', '95'])).
% 0.99/1.17  thf(d5_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.99/1.17  thf('100', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.99/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.99/1.17  thf('101', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['99', '100'])).
% 0.99/1.17  thf(t3_boole, axiom,
% 0.99/1.17    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.17  thf('102', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.17  thf('103', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['101', '102'])).
% 0.99/1.17  thf('104', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['98', '103'])).
% 0.99/1.17  thf(d10_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.17  thf('105', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.17  thf('106', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.99/1.17      inference('simplify', [status(thm)], ['105'])).
% 0.99/1.17  thf('107', plain,
% 0.99/1.17      (![X34 : $i, X36 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.99/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.17  thf('108', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['106', '107'])).
% 0.99/1.17  thf('109', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.99/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.99/1.17  thf('110', plain,
% 0.99/1.17      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['108', '109'])).
% 0.99/1.17  thf('111', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.99/1.17      inference('simplify', [status(thm)], ['105'])).
% 0.99/1.17  thf('112', plain,
% 0.99/1.17      (![X13 : $i, X14 : $i]:
% 0.99/1.17         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.99/1.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.99/1.17  thf('113', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['111', '112'])).
% 0.99/1.17  thf('114', plain,
% 0.99/1.17      (![X5 : $i, X6 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ X5 @ X6)
% 0.99/1.17           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.99/1.17  thf('115', plain,
% 0.99/1.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['113', '114'])).
% 0.99/1.17  thf('116', plain,
% 0.99/1.17      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['110', '115'])).
% 0.99/1.17  thf('117', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['104', '116'])).
% 0.99/1.17  thf('118', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.99/1.17      inference('demod', [status(thm)], ['85', '117'])).
% 0.99/1.17  thf('119', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['80', '118'])).
% 0.99/1.17  thf(t39_xboole_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.17  thf('120', plain,
% 0.99/1.17      (![X17 : $i, X18 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.99/1.17           = (k2_xboole_0 @ X17 @ X18))),
% 0.99/1.17      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.99/1.17  thf('121', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.99/1.17           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['119', '120'])).
% 0.99/1.17  thf('122', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.99/1.17      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.17  thf('123', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['121', '122'])).
% 0.99/1.17  thf('124', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17           (k3_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['79', '123'])).
% 0.99/1.17  thf('125', plain,
% 0.99/1.17      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17          = (sk_B)))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['64', '124'])).
% 0.99/1.17  thf('126', plain,
% 0.99/1.17      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['55', '125'])).
% 0.99/1.17  thf('127', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t52_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.99/1.17             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.99/1.17               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('128', plain,
% 0.99/1.17      (![X37 : $i, X38 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.99/1.17          | ~ (v2_pre_topc @ X38)
% 0.99/1.17          | ((k2_pre_topc @ X38 @ X37) != (X37))
% 0.99/1.17          | (v4_pre_topc @ X37 @ X38)
% 0.99/1.17          | ~ (l1_pre_topc @ X38))),
% 0.99/1.17      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.99/1.17  thf('129', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.17        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['127', '128'])).
% 0.99/1.17  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('132', plain,
% 0.99/1.17      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.99/1.17  thf('133', plain,
% 0.99/1.17      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['126', '132'])).
% 0.99/1.17  thf('134', plain,
% 0.99/1.17      (((v4_pre_topc @ sk_B @ sk_A))
% 0.99/1.17         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('simplify', [status(thm)], ['133'])).
% 0.99/1.17  thf('135', plain,
% 0.99/1.17      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.17      inference('split', [status(esa)], ['49'])).
% 0.99/1.17  thf('136', plain,
% 0.99/1.17      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.99/1.17       ~
% 0.99/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['134', '135'])).
% 0.99/1.17  thf('137', plain,
% 0.99/1.17      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.99/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('split', [status(esa)], ['37'])).
% 0.99/1.17  thf('138', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['50', '136', '137'])).
% 0.99/1.17  thf('139', plain,
% 0.99/1.17      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('simpl_trail', [status(thm)], ['48', '138'])).
% 0.99/1.17  thf('140', plain,
% 0.99/1.17      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['35', '36', '139'])).
% 0.99/1.17  thf('141', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17              (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= (~
% 0.99/1.17             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('split', [status(esa)], ['49'])).
% 0.99/1.17  thf('142', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.17           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf('143', plain,
% 0.99/1.17      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.17         <= (~
% 0.99/1.17             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('demod', [status(thm)], ['141', '142'])).
% 0.99/1.17  thf('144', plain,
% 0.99/1.17      (~
% 0.99/1.17       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.17             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['50', '136'])).
% 0.99/1.17  thf('145', plain,
% 0.99/1.17      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('simpl_trail', [status(thm)], ['143', '144'])).
% 0.99/1.17  thf('146', plain, ($false),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['140', '145'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
