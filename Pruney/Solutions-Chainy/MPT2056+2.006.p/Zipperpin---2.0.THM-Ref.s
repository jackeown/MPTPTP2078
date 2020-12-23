%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3IbLH4YhCl

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 220 expanded)
%              Number of leaves         :   44 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          : 1041 (2444 expanded)
%              Number of equality atoms :   69 ( 145 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ X2 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X3 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('44',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) ) @ X27 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X28 @ ( k3_yellow19 @ X28 @ ( k2_struct_0 @ X28 ) @ X27 ) ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) ) @ X27 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X28 @ ( k3_yellow19 @ X28 @ ( k2_struct_0 @ X28 ) @ X27 ) ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','56','59','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','67'])).

thf('69',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','68'])).

thf('70',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t2_yellow19,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf('72',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_yellow_1 @ X30 ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_yellow_1 @ X30 ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_yellow_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X30 ) ) ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('76',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('77',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('80',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('81',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','84'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('90',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3IbLH4YhCl
% 0.16/0.35  % Computer   : n009.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 17:47:26 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 610 iterations in 0.174s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.46/0.64  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.46/0.64  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.46/0.64  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.46/0.64  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t15_yellow19, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64             ( v1_subset_1 @
% 0.46/0.64               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.64             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64             ( m1_subset_1 @
% 0.46/0.64               B @ 
% 0.46/0.64               ( k1_zfmisc_1 @
% 0.46/0.64                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.64           ( ( B ) =
% 0.46/0.64             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64                ( v1_subset_1 @
% 0.46/0.64                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.64                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64                ( m1_subset_1 @
% 0.46/0.64                  B @ 
% 0.46/0.64                  ( k1_zfmisc_1 @
% 0.46/0.64                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.64              ( ( B ) =
% 0.46/0.64                ( k2_yellow19 @
% 0.46/0.64                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.46/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(l27_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ (k1_tarski @ X20) @ X21) | (r2_hidden @ X20 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf(t4_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.46/0.64          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.64          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0)
% 0.46/0.64          | (r1_tarski @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.64           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf(t3_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('7', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.64           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.64           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf(t4_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_boole])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.64  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '14'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.64           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('20', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_boole])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('26', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X10 : $i, X12 : $i]:
% 0.46/0.64         (((X10) = (X12))
% 0.46/0.64          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.64          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.46/0.64          | ((X2) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.46/0.64          | ((X2) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         ((r2_hidden @ X3 @ X2)
% 0.46/0.64          | ((k3_xboole_0 @ (k1_tarski @ X3) @ X2) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.46/0.64            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['31', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf('39', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.46/0.64          | (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (((sk_B)
% 0.46/0.64         != (k2_yellow19 @ sk_A @ 
% 0.46/0.64             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d2_yellow_1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(t14_yellow19, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.64             ( m1_subset_1 @
% 0.46/0.64               B @ 
% 0.46/0.64               ( k1_zfmisc_1 @
% 0.46/0.64                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.64           ( ( k7_subset_1 @
% 0.46/0.64               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.46/0.64               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.46/0.64             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X27)
% 0.46/0.64          | ~ (v2_waybel_0 @ X27 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))
% 0.46/0.64          | ~ (v13_waybel_0 @ X27 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))))
% 0.46/0.64          | ((k7_subset_1 @ 
% 0.46/0.64              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X28))) @ X27 @ 
% 0.46/0.64              (k1_tarski @ k1_xboole_0))
% 0.46/0.64              = (k2_yellow19 @ X28 @ 
% 0.46/0.64                 (k3_yellow19 @ X28 @ (k2_struct_0 @ X28) @ X27)))
% 0.46/0.64          | ~ (l1_struct_0 @ X28)
% 0.46/0.64          | (v2_struct_0 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X27)
% 0.46/0.64          | ~ (v2_waybel_0 @ X27 @ 
% 0.46/0.64               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))
% 0.46/0.64          | ~ (v13_waybel_0 @ X27 @ 
% 0.46/0.64               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (u1_struct_0 @ 
% 0.46/0.64                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))))
% 0.46/0.64          | ((k7_subset_1 @ 
% 0.46/0.64              (u1_struct_0 @ 
% 0.46/0.64               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28)))) @ 
% 0.46/0.64              X27 @ (k1_tarski @ k1_xboole_0))
% 0.46/0.64              = (k2_yellow19 @ X28 @ 
% 0.46/0.64                 (k3_yellow19 @ X28 @ (k2_struct_0 @ X28) @ X27)))
% 0.46/0.64          | ~ (l1_struct_0 @ X28)
% 0.46/0.64          | (v2_struct_0 @ X28))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.64        | ((k7_subset_1 @ 
% 0.46/0.64            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.46/0.64            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.46/0.64            = (k2_yellow19 @ sk_A @ 
% 0.46/0.64               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.46/0.64        | ~ (v13_waybel_0 @ sk_B @ 
% 0.46/0.64             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.64        | ~ (v2_waybel_0 @ sk_B @ 
% 0.46/0.64             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.64        | (v1_xboole_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['45', '51'])).
% 0.46/0.64  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.64       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.46/0.64          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k7_subset_1 @ 
% 0.46/0.64           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.46/0.64           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((v13_waybel_0 @ sk_B @ 
% 0.46/0.64        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      ((v2_waybel_0 @ sk_B @ 
% 0.46/0.64        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.46/0.64            = (k2_yellow19 @ sk_A @ 
% 0.46/0.64               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.46/0.64        | (v1_xboole_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53', '56', '59', '62'])).
% 0.46/0.64  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_B)
% 0.46/0.64        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.46/0.64            = (k2_yellow19 @ sk_A @ 
% 0.46/0.64               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.46/0.64      inference('clc', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.46/0.64         = (k2_yellow19 @ sk_A @ 
% 0.46/0.64            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.46/0.64      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['42', '67'])).
% 0.46/0.64  thf('69', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '68'])).
% 0.46/0.64  thf('70', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.46/0.64      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(t2_yellow19, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.46/0.64             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.46/0.64             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.46/0.64             ( m1_subset_1 @
% 0.46/0.64               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.46/0.64           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X29)
% 0.46/0.64          | ~ (v1_subset_1 @ X29 @ (u1_struct_0 @ (k3_yellow_1 @ X30)))
% 0.46/0.64          | ~ (v2_waybel_0 @ X29 @ (k3_yellow_1 @ X30))
% 0.46/0.64          | ~ (v13_waybel_0 @ X29 @ (k3_yellow_1 @ X30))
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ 
% 0.46/0.64               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X30))))
% 0.46/0.64          | ~ (r2_hidden @ X31 @ X29)
% 0.46/0.64          | ~ (v1_xboole_0 @ X31)
% 0.46/0.64          | (v1_xboole_0 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X29)
% 0.46/0.64          | ~ (v1_subset_1 @ X29 @ 
% 0.46/0.64               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X30))))
% 0.46/0.64          | ~ (v2_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X30)))
% 0.46/0.64          | ~ (v13_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X30)))
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X30)))))
% 0.46/0.64          | ~ (r2_hidden @ X31 @ X29)
% 0.46/0.64          | ~ (v1_xboole_0 @ X31)
% 0.46/0.64          | (v1_xboole_0 @ X30))),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.64          | ~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.64          | ~ (v13_waybel_0 @ sk_B @ 
% 0.46/0.64               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.64          | ~ (v2_waybel_0 @ sk_B @ 
% 0.46/0.64               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.64          | ~ (v1_subset_1 @ sk_B @ 
% 0.46/0.64               (u1_struct_0 @ 
% 0.46/0.64                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.46/0.64          | (v1_xboole_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      ((v13_waybel_0 @ sk_B @ 
% 0.46/0.64        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((v2_waybel_0 @ sk_B @ 
% 0.46/0.64        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((v1_subset_1 @ sk_B @ 
% 0.46/0.64        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      ((v1_subset_1 @ sk_B @ 
% 0.46/0.64        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.64          | ~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.64          | (v1_xboole_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['78', '79', '80', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_B)
% 0.46/0.64        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['70', '84'])).
% 0.46/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.64  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('89', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['87', '88'])).
% 0.46/0.64  thf(fc5_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (![X25 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 0.46/0.64          | ~ (l1_struct_0 @ X25)
% 0.46/0.64          | (v2_struct_0 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.64  thf('91', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.64  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('93', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.64  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
