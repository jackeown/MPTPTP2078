%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pr3s4jzcTg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 190 expanded)
%              Number of leaves         :   47 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  982 (2281 expanded)
%              Number of equality atoms :   55 ( 106 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
      | ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('31',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) @ X31 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('34',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) @ X31 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40','43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','55'])).

thf('57',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','56'])).

thf('58',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('60',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_yellow_1 @ X34 ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_yellow_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) ) ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('68',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('69',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('71',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pr3s4jzcTg
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.74/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.96  % Solved by: fo/fo7.sh
% 0.74/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.96  % done 1127 iterations in 0.465s
% 0.74/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.96  % SZS output start Refutation
% 0.74/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.96  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.74/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.96  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.74/0.96  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.74/0.96  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/0.96  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.74/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.96  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.74/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.96  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.74/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.74/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.96  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.74/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.96  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.74/0.96  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.74/0.96  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.74/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.74/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.96  thf(t15_yellow19, conjecture,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.74/0.96       ( ![B:$i]:
% 0.74/0.96         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.74/0.96             ( v1_subset_1 @
% 0.74/0.96               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.74/0.96             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97             ( m1_subset_1 @
% 0.74/0.97               B @ 
% 0.74/0.97               ( k1_zfmisc_1 @
% 0.74/0.97                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.74/0.97           ( ( B ) =
% 0.74/0.97             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.74/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.97    (~( ![A:$i]:
% 0.74/0.97        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.74/0.97          ( ![B:$i]:
% 0.74/0.97            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.74/0.97                ( v1_subset_1 @
% 0.74/0.97                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.74/0.97                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97                ( m1_subset_1 @
% 0.74/0.97                  B @ 
% 0.74/0.97                  ( k1_zfmisc_1 @
% 0.74/0.97                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.74/0.97              ( ( B ) =
% 0.74/0.97                ( k2_yellow19 @
% 0.74/0.97                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.74/0.97    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.74/0.97  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf(d3_struct_0, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.74/0.97  thf('1', plain,
% 0.74/0.97      (![X28 : $i]:
% 0.74/0.97         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.74/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/0.97  thf(l27_zfmisc_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.74/0.97  thf('2', plain,
% 0.74/0.97      (![X23 : $i, X24 : $i]:
% 0.74/0.97         ((r1_xboole_0 @ (k1_tarski @ X23) @ X24) | (r2_hidden @ X23 @ X24))),
% 0.74/0.97      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.74/0.97  thf(d1_xboole_0, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.97  thf('3', plain,
% 0.74/0.97      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.74/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.97  thf(t4_xboole_0, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.97            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.97  thf('4', plain,
% 0.74/0.97      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.74/0.97         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.74/0.97          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.74/0.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.97  thf('5', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.97  thf('6', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((r2_hidden @ X1 @ X0)
% 0.74/0.97          | (v1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['2', '5'])).
% 0.74/0.97  thf(d3_tarski, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.97  thf('7', plain,
% 0.74/0.97      (![X6 : $i, X8 : $i]:
% 0.74/0.97         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.74/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.97  thf('8', plain,
% 0.74/0.97      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.74/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.97  thf('9', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.97  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.74/0.97  thf('10', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.74/0.97      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.97  thf(d10_xboole_0, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.97  thf('11', plain,
% 0.74/0.97      (![X13 : $i, X15 : $i]:
% 0.74/0.97         (((X13) = (X15))
% 0.74/0.97          | ~ (r1_tarski @ X15 @ X13)
% 0.74/0.97          | ~ (r1_tarski @ X13 @ X15))),
% 0.74/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.97  thf('12', plain,
% 0.74/0.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.97  thf('13', plain,
% 0.74/0.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['9', '12'])).
% 0.74/0.97  thf(t48_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.97  thf('14', plain,
% 0.74/0.97      (![X20 : $i, X21 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.74/0.97           = (k3_xboole_0 @ X20 @ X21))),
% 0.74/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.97  thf(t4_boole, axiom,
% 0.74/0.97    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.74/0.97  thf('15', plain,
% 0.74/0.97      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.74/0.97      inference('cnf', [status(esa)], [t4_boole])).
% 0.74/0.97  thf('16', plain,
% 0.74/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['14', '15'])).
% 0.74/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.74/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.74/0.97  thf('17', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.97  thf('18', plain,
% 0.74/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['16', '17'])).
% 0.74/0.97  thf(t100_xboole_1, axiom,
% 0.74/0.97    (![A:$i,B:$i]:
% 0.74/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/0.97  thf('19', plain,
% 0.74/0.97      (![X16 : $i, X17 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X16 @ X17)
% 0.74/0.97           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.74/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.97  thf('20', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['18', '19'])).
% 0.74/0.97  thf(t3_boole, axiom,
% 0.74/0.97    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.97  thf('21', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.74/0.97      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.97  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['20', '21'])).
% 0.74/0.97  thf('23', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.97      inference('sup+', [status(thm)], ['13', '22'])).
% 0.74/0.97  thf('24', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.97  thf('25', plain,
% 0.74/0.97      (![X16 : $i, X17 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X16 @ X17)
% 0.74/0.97           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.74/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.97  thf('26', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.74/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.74/0.97      inference('sup+', [status(thm)], ['24', '25'])).
% 0.74/0.97  thf('27', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.74/0.97          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.74/0.97      inference('sup+', [status(thm)], ['23', '26'])).
% 0.74/0.97  thf('28', plain,
% 0.74/0.97      (![X0 : $i, X1 : $i]:
% 0.74/0.97         ((r2_hidden @ X1 @ X0)
% 0.74/0.97          | ((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['6', '27'])).
% 0.74/0.97  thf('29', plain,
% 0.74/0.97      (((sk_B_1)
% 0.74/0.97         != (k2_yellow19 @ sk_A @ 
% 0.74/0.97             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('30', plain,
% 0.74/0.97      ((m1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf(d2_yellow_1, axiom,
% 0.74/0.97    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.74/0.97  thf('31', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('32', plain,
% 0.74/0.97      ((m1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (k1_zfmisc_1 @ 
% 0.74/0.97         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.74/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.74/0.97  thf(t14_yellow19, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.74/0.97       ( ![B:$i]:
% 0.74/0.97         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.74/0.97             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.74/0.97             ( m1_subset_1 @
% 0.74/0.97               B @ 
% 0.74/0.97               ( k1_zfmisc_1 @
% 0.74/0.97                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.74/0.97           ( ( k7_subset_1 @
% 0.74/0.97               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.74/0.97               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.74/0.97             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.74/0.97  thf('33', plain,
% 0.74/0.97      (![X31 : $i, X32 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ X31)
% 0.74/0.97          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.74/0.97          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.74/0.97          | ~ (m1_subset_1 @ X31 @ 
% 0.74/0.97               (k1_zfmisc_1 @ 
% 0.74/0.97                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))))
% 0.74/0.97          | ((k7_subset_1 @ 
% 0.74/0.97              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32))) @ X31 @ 
% 0.74/0.97              (k1_tarski @ k1_xboole_0))
% 0.74/0.97              = (k2_yellow19 @ X32 @ 
% 0.74/0.97                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.74/0.97          | ~ (l1_struct_0 @ X32)
% 0.74/0.97          | (v2_struct_0 @ X32))),
% 0.74/0.97      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.74/0.97  thf('34', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('35', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('36', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('37', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('38', plain,
% 0.74/0.97      (![X31 : $i, X32 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ X31)
% 0.74/0.97          | ~ (v2_waybel_0 @ X31 @ 
% 0.74/0.97               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.74/0.97          | ~ (v13_waybel_0 @ X31 @ 
% 0.74/0.97               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.74/0.97          | ~ (m1_subset_1 @ X31 @ 
% 0.74/0.97               (k1_zfmisc_1 @ 
% 0.74/0.97                (u1_struct_0 @ 
% 0.74/0.97                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))))
% 0.74/0.97          | ((k7_subset_1 @ 
% 0.74/0.97              (u1_struct_0 @ 
% 0.74/0.97               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32)))) @ 
% 0.74/0.97              X31 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97              = (k2_yellow19 @ X32 @ 
% 0.74/0.97                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.74/0.97          | ~ (l1_struct_0 @ X32)
% 0.74/0.97          | (v2_struct_0 @ X32))),
% 0.74/0.97      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.74/0.97  thf('39', plain,
% 0.74/0.97      (((v2_struct_0 @ sk_A)
% 0.74/0.97        | ~ (l1_struct_0 @ sk_A)
% 0.74/0.97        | ((k7_subset_1 @ 
% 0.74/0.97            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.74/0.97            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97            = (k2_yellow19 @ sk_A @ 
% 0.74/0.97               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.74/0.97        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.74/0.97             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.74/0.97        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.74/0.97             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.74/0.97        | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('sup-', [status(thm)], ['32', '38'])).
% 0.74/0.97  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('41', plain,
% 0.74/0.97      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('42', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('43', plain,
% 0.74/0.97      ((v13_waybel_0 @ sk_B_1 @ 
% 0.74/0.97        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.74/0.97      inference('demod', [status(thm)], ['41', '42'])).
% 0.74/0.97  thf('44', plain,
% 0.74/0.97      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('45', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('46', plain,
% 0.74/0.97      ((v2_waybel_0 @ sk_B_1 @ 
% 0.74/0.97        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.74/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/0.97  thf('47', plain,
% 0.74/0.97      (((v2_struct_0 @ sk_A)
% 0.74/0.97        | ((k7_subset_1 @ 
% 0.74/0.97            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.74/0.97            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97            = (k2_yellow19 @ sk_A @ 
% 0.74/0.97               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.74/0.97        | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('demod', [status(thm)], ['39', '40', '43', '46'])).
% 0.74/0.97  thf('48', plain,
% 0.74/0.97      ((m1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (k1_zfmisc_1 @ 
% 0.74/0.97         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.74/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.74/0.97  thf(redefinition_k7_subset_1, axiom,
% 0.74/0.97    (![A:$i,B:$i,C:$i]:
% 0.74/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.97       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.74/0.97  thf('49', plain,
% 0.74/0.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.97         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.74/0.97          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.74/0.97      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.74/0.97  thf('50', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((k7_subset_1 @ 
% 0.74/0.97           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.74/0.97           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.74/0.97      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/0.97  thf('51', plain,
% 0.74/0.97      (((v2_struct_0 @ sk_A)
% 0.74/0.97        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97            = (k2_yellow19 @ sk_A @ 
% 0.74/0.97               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.74/0.97        | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('demod', [status(thm)], ['47', '50'])).
% 0.74/0.97  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('53', plain,
% 0.74/0.97      (((v1_xboole_0 @ sk_B_1)
% 0.74/0.97        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97            = (k2_yellow19 @ sk_A @ 
% 0.74/0.97               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.74/0.97      inference('clc', [status(thm)], ['51', '52'])).
% 0.74/0.97  thf('54', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('55', plain,
% 0.74/0.97      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.74/0.97         = (k2_yellow19 @ sk_A @ 
% 0.74/0.97            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.74/0.97      inference('clc', [status(thm)], ['53', '54'])).
% 0.74/0.97  thf('56', plain,
% 0.74/0.97      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.74/0.97      inference('demod', [status(thm)], ['29', '55'])).
% 0.74/0.97  thf('57', plain,
% 0.74/0.97      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('sup-', [status(thm)], ['28', '56'])).
% 0.74/0.97  thf('58', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.74/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.74/0.97  thf('59', plain,
% 0.74/0.97      ((m1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (k1_zfmisc_1 @ 
% 0.74/0.97         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.74/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.74/0.97  thf(t2_yellow19, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.74/0.97       ( ![B:$i]:
% 0.74/0.97         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.74/0.97             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.74/0.97             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.74/0.97             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.74/0.97             ( m1_subset_1 @
% 0.74/0.97               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.74/0.97           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.74/0.97  thf('60', plain,
% 0.74/0.97      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ X33)
% 0.74/0.97          | ~ (v1_subset_1 @ X33 @ (u1_struct_0 @ (k3_yellow_1 @ X34)))
% 0.74/0.97          | ~ (v2_waybel_0 @ X33 @ (k3_yellow_1 @ X34))
% 0.74/0.97          | ~ (v13_waybel_0 @ X33 @ (k3_yellow_1 @ X34))
% 0.74/0.97          | ~ (m1_subset_1 @ X33 @ 
% 0.74/0.97               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X34))))
% 0.74/0.97          | ~ (r2_hidden @ X35 @ X33)
% 0.74/0.97          | ~ (v1_xboole_0 @ X35)
% 0.74/0.97          | (v1_xboole_0 @ X34))),
% 0.74/0.97      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.74/0.97  thf('61', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('62', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('63', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('64', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('65', plain,
% 0.74/0.97      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ X33)
% 0.74/0.97          | ~ (v1_subset_1 @ X33 @ 
% 0.74/0.97               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34))))
% 0.74/0.97          | ~ (v2_waybel_0 @ X33 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.74/0.97          | ~ (v13_waybel_0 @ X33 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.74/0.97          | ~ (m1_subset_1 @ X33 @ 
% 0.74/0.97               (k1_zfmisc_1 @ 
% 0.74/0.97                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))))
% 0.74/0.97          | ~ (r2_hidden @ X35 @ X33)
% 0.74/0.97          | ~ (v1_xboole_0 @ X35)
% 0.74/0.97          | (v1_xboole_0 @ X34))),
% 0.74/0.97      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.74/0.97  thf('66', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.74/0.97          | ~ (v1_xboole_0 @ X0)
% 0.74/0.97          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.74/0.97          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.74/0.97               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.74/0.97          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.74/0.97               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.74/0.97          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.74/0.97               (u1_struct_0 @ 
% 0.74/0.97                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.74/0.97          | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('sup-', [status(thm)], ['59', '65'])).
% 0.74/0.97  thf('67', plain,
% 0.74/0.97      ((v13_waybel_0 @ sk_B_1 @ 
% 0.74/0.97        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.74/0.97      inference('demod', [status(thm)], ['41', '42'])).
% 0.74/0.97  thf('68', plain,
% 0.74/0.97      ((v2_waybel_0 @ sk_B_1 @ 
% 0.74/0.97        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.74/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/0.97  thf('69', plain,
% 0.74/0.97      ((v1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('70', plain,
% 0.74/0.97      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.74/0.97      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.74/0.97  thf('71', plain,
% 0.74/0.97      ((v1_subset_1 @ sk_B_1 @ 
% 0.74/0.97        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.74/0.97      inference('demod', [status(thm)], ['69', '70'])).
% 0.74/0.97  thf('72', plain,
% 0.74/0.97      (![X0 : $i]:
% 0.74/0.97         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.74/0.97          | ~ (v1_xboole_0 @ X0)
% 0.74/0.97          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.74/0.97          | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.97      inference('demod', [status(thm)], ['66', '67', '68', '71'])).
% 0.74/0.97  thf('73', plain,
% 0.74/0.97      (((v1_xboole_0 @ sk_B_1)
% 0.74/0.97        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.74/0.97        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.74/0.97      inference('sup-', [status(thm)], ['58', '72'])).
% 0.74/0.97  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.74/0.97  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.97  thf('75', plain,
% 0.74/0.97      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.74/0.97      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/0.97  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('77', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.74/0.97      inference('clc', [status(thm)], ['75', '76'])).
% 0.74/0.97  thf('78', plain,
% 0.74/0.97      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.74/0.97      inference('sup+', [status(thm)], ['1', '77'])).
% 0.74/0.97  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('80', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.74/0.97      inference('demod', [status(thm)], ['78', '79'])).
% 0.74/0.97  thf(fc2_struct_0, axiom,
% 0.74/0.97    (![A:$i]:
% 0.74/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.74/0.97       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.74/0.97  thf('81', plain,
% 0.74/0.97      (![X29 : $i]:
% 0.74/0.97         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.74/0.97          | ~ (l1_struct_0 @ X29)
% 0.74/0.97          | (v2_struct_0 @ X29))),
% 0.74/0.97      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.74/0.97  thf('82', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.74/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.74/0.97  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.74/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.97  thf('84', plain, ((v2_struct_0 @ sk_A)),
% 0.74/0.97      inference('demod', [status(thm)], ['82', '83'])).
% 0.74/0.97  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 0.74/0.97  
% 0.74/0.97  % SZS output end Refutation
% 0.74/0.97  
% 0.74/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
