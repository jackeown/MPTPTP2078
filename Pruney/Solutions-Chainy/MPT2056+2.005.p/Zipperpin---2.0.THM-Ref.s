%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7I4KzANXD5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 310 expanded)
%              Number of leaves         :   45 ( 117 expanded)
%              Depth                    :   28
%              Number of atoms          : 1261 (3416 expanded)
%              Number of equality atoms :   71 ( 186 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k4_xboole_0 @ X31 @ ( k1_tarski @ X33 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X16 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

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
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X32 )
      | ~ ( r2_hidden @ X30 @ ( k4_xboole_0 @ X31 @ ( k1_tarski @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X31 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('60',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

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

thf('62',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v2_waybel_0 @ X40 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) )
      | ~ ( v13_waybel_0 @ X40 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) ) @ X40 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X41 @ ( k3_yellow19 @ X41 @ ( k2_struct_0 @ X41 ) @ X40 ) ) )
      | ~ ( l1_struct_0 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('63',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('67',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v2_waybel_0 @ X40 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) )
      | ~ ( v13_waybel_0 @ X40 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) ) @ X40 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X41 @ ( k3_yellow19 @ X41 @ ( k2_struct_0 @ X41 ) @ X40 ) ) )
      | ~ ( l1_struct_0 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('71',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','72','75','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','83'])).

thf('85',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','84'])).

thf('86',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

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

thf('88',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( v1_subset_1 @ X42 @ ( u1_struct_0 @ ( k3_yellow_1 @ X43 ) ) )
      | ~ ( v2_waybel_0 @ X42 @ ( k3_yellow_1 @ X43 ) )
      | ~ ( v13_waybel_0 @ X42 @ ( k3_yellow_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X43 ) ) ) )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ~ ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('89',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('90',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('91',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('92',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('93',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( v1_subset_1 @ X42 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) ) )
      | ~ ( v2_waybel_0 @ X42 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) )
      | ~ ( v13_waybel_0 @ X42 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) ) ) )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ~ ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('96',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('97',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','100'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('109',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7I4KzANXD5
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:01:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.81/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/0.98  % Solved by: fo/fo7.sh
% 0.81/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/0.98  % done 1237 iterations in 0.525s
% 0.81/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/0.98  % SZS output start Refutation
% 0.81/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.81/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/0.98  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.81/0.98  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.81/0.98  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.81/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/0.98  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.81/0.98  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.81/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/0.98  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.81/0.98  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.81/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/0.98  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.81/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.81/0.98  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.81/0.98  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.81/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.81/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.81/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/0.98  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.81/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.81/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.81/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/0.98  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.81/0.98  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.81/0.98  thf(t15_yellow19, conjecture,
% 0.81/0.98    (![A:$i]:
% 0.81/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.81/0.98       ( ![B:$i]:
% 0.81/0.98         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/0.98             ( v1_subset_1 @
% 0.81/0.98               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.81/0.98             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98             ( m1_subset_1 @
% 0.81/0.98               B @ 
% 0.81/0.98               ( k1_zfmisc_1 @
% 0.81/0.98                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.81/0.98           ( ( B ) =
% 0.81/0.98             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.81/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.81/0.98    (~( ![A:$i]:
% 0.81/0.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.81/0.98          ( ![B:$i]:
% 0.81/0.98            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/0.98                ( v1_subset_1 @
% 0.81/0.98                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.81/0.98                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98                ( m1_subset_1 @
% 0.81/0.98                  B @ 
% 0.81/0.98                  ( k1_zfmisc_1 @
% 0.81/0.98                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.81/0.98              ( ( B ) =
% 0.81/0.98                ( k2_yellow19 @
% 0.81/0.98                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.81/0.98    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.81/0.98  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf(d3_struct_0, axiom,
% 0.81/0.98    (![A:$i]:
% 0.81/0.98     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.81/0.98  thf('1', plain,
% 0.81/0.98      (![X37 : $i]:
% 0.81/0.98         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.81/0.98      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.81/0.98  thf(t3_xboole_0, axiom,
% 0.81/0.98    (![A:$i,B:$i]:
% 0.81/0.98     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.81/0.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.81/0.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.81/0.98            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.81/0.98  thf('2', plain,
% 0.81/0.98      (![X12 : $i, X13 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.81/0.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/0.98  thf(t64_zfmisc_1, axiom,
% 0.81/0.98    (![A:$i,B:$i,C:$i]:
% 0.81/0.98     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.81/0.98       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.81/0.98  thf('3', plain,
% 0.81/0.98      (![X30 : $i, X31 : $i, X33 : $i]:
% 0.81/0.98         ((r2_hidden @ X30 @ (k4_xboole_0 @ X31 @ (k1_tarski @ X33)))
% 0.81/0.98          | ((X30) = (X33))
% 0.81/0.98          | ~ (r2_hidden @ X30 @ X31))),
% 0.81/0.98      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.81/0.98  thf('4', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X0 @ X1)
% 0.81/0.98          | ((sk_C_1 @ X1 @ X0) = (X2))
% 0.81/0.98          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ 
% 0.81/0.98             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 0.81/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/0.98  thf('5', plain,
% 0.81/0.98      (![X12 : $i, X13 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.81/0.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/0.98  thf('6', plain,
% 0.81/0.98      (![X12 : $i, X13 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 0.81/0.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/0.98  thf(d5_xboole_0, axiom,
% 0.81/0.98    (![A:$i,B:$i,C:$i]:
% 0.81/0.98     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.81/0.98       ( ![D:$i]:
% 0.81/0.98         ( ( r2_hidden @ D @ C ) <=>
% 0.81/0.98           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.81/0.98  thf('7', plain,
% 0.81/0.98      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X10 @ X9)
% 0.81/0.98          | ~ (r2_hidden @ X10 @ X8)
% 0.81/0.98          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/0.98  thf('8', plain,
% 0.81/0.98      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X10 @ X8)
% 0.81/0.98          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.81/0.98      inference('simplify', [status(thm)], ['7'])).
% 0.81/0.98  thf('9', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.81/0.98          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['6', '8'])).
% 0.81/0.98  thf('10', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.81/0.98          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['5', '9'])).
% 0.81/0.98  thf('11', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.81/0.98      inference('simplify', [status(thm)], ['10'])).
% 0.81/0.98  thf(t4_xboole_0, axiom,
% 0.81/0.98    (![A:$i,B:$i]:
% 0.81/0.98     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.81/0.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.81/0.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.81/0.98            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.81/0.98  thf('12', plain,
% 0.81/0.98      (![X16 : $i, X17 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X16 @ X17)
% 0.81/0.98          | (r2_hidden @ (sk_C_2 @ X17 @ X16) @ (k3_xboole_0 @ X16 @ X17)))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/0.98  thf(commutativity_k3_xboole_0, axiom,
% 0.81/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.81/0.98  thf('13', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/0.98  thf('14', plain,
% 0.81/0.98      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.81/0.98          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/0.98  thf('15', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.81/0.98          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/0.98  thf('16', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('sup-', [status(thm)], ['12', '15'])).
% 0.81/0.98  thf('17', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['11', '16'])).
% 0.81/0.98  thf('18', plain,
% 0.81/0.98      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.81/0.98         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.81/0.98          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.81/0.98          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.81/0.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.81/0.98  thf(t4_boole, axiom,
% 0.81/0.98    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.81/0.98  thf('19', plain,
% 0.81/0.98      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_boole])).
% 0.81/0.98  thf('20', plain,
% 0.81/0.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.81/0.98         (((X30) != (X32))
% 0.81/0.98          | ~ (r2_hidden @ X30 @ (k4_xboole_0 @ X31 @ (k1_tarski @ X32))))),
% 0.81/0.98      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.81/0.98  thf('21', plain,
% 0.81/0.98      (![X31 : $i, X32 : $i]:
% 0.81/0.98         ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X31 @ (k1_tarski @ X32)))),
% 0.81/0.98      inference('simplify', [status(thm)], ['20'])).
% 0.81/0.98  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.81/0.98      inference('sup-', [status(thm)], ['19', '21'])).
% 0.81/0.98  thf('23', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/0.98          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.81/0.98      inference('sup-', [status(thm)], ['18', '22'])).
% 0.81/0.98  thf('24', plain,
% 0.81/0.98      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_boole])).
% 0.81/0.98  thf('25', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/0.98          | ((X1) = (k1_xboole_0)))),
% 0.81/0.98      inference('demod', [status(thm)], ['23', '24'])).
% 0.81/0.98  thf('26', plain,
% 0.81/0.98      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.81/0.98          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/0.98  thf('27', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.81/0.98  thf('28', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['17', '27'])).
% 0.81/0.98  thf(t100_xboole_1, axiom,
% 0.81/0.98    (![A:$i,B:$i]:
% 0.81/0.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.81/0.98  thf('29', plain,
% 0.81/0.98      (![X23 : $i, X24 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X23 @ X24)
% 0.81/0.98           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.81/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/0.98  thf('30', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.81/0.98           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['28', '29'])).
% 0.81/0.98  thf(t48_xboole_1, axiom,
% 0.81/0.98    (![A:$i,B:$i]:
% 0.81/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/0.98  thf('31', plain,
% 0.81/0.98      (![X27 : $i, X28 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 0.81/0.98           = (k3_xboole_0 @ X27 @ X28))),
% 0.81/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/0.98  thf('32', plain,
% 0.81/0.98      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.81/0.98      inference('cnf', [status(esa)], [t4_boole])).
% 0.81/0.98  thf('33', plain,
% 0.81/0.98      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['31', '32'])).
% 0.81/0.98  thf('34', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/0.98  thf('35', plain,
% 0.81/0.98      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['33', '34'])).
% 0.81/0.98  thf('36', plain,
% 0.81/0.98      (![X23 : $i, X24 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X23 @ X24)
% 0.81/0.98           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.81/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/0.98  thf('37', plain,
% 0.81/0.98      (![X0 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['35', '36'])).
% 0.81/0.98  thf(t3_boole, axiom,
% 0.81/0.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.81/0.98  thf('38', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.81/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.81/0.98  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['37', '38'])).
% 0.81/0.98  thf('40', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.81/0.98      inference('demod', [status(thm)], ['30', '39'])).
% 0.81/0.98  thf('41', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.81/0.98          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['6', '8'])).
% 0.81/0.98  thf('42', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         (~ (r2_hidden @ (sk_C_1 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.81/0.98          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 0.81/0.98      inference('sup-', [status(thm)], ['40', '41'])).
% 0.81/0.98  thf('43', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.81/0.98      inference('demod', [status(thm)], ['30', '39'])).
% 0.81/0.98  thf('44', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         (~ (r2_hidden @ (sk_C_1 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.81/0.98          | (r1_xboole_0 @ X0 @ X2))),
% 0.81/0.98      inference('demod', [status(thm)], ['42', '43'])).
% 0.81/0.98  thf('45', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         (((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.81/0.98          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.81/0.98          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.81/0.98      inference('sup-', [status(thm)], ['4', '44'])).
% 0.81/0.98  thf('46', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.81/0.98          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.81/0.98      inference('simplify', [status(thm)], ['45'])).
% 0.81/0.98  thf('47', plain,
% 0.81/0.98      (![X12 : $i, X13 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X13))),
% 0.81/0.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/0.98  thf('48', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r2_hidden @ X0 @ X1)
% 0.81/0.98          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.81/0.98          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.81/0.98      inference('sup+', [status(thm)], ['46', '47'])).
% 0.81/0.98  thf('49', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.81/0.98      inference('simplify', [status(thm)], ['48'])).
% 0.81/0.98  thf('50', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.81/0.98          | ((X1) = (k1_xboole_0)))),
% 0.81/0.98      inference('demod', [status(thm)], ['23', '24'])).
% 0.81/0.98  thf('51', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.98         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.81/0.98          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/0.98  thf('52', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.98      inference('sup-', [status(thm)], ['50', '51'])).
% 0.81/0.98  thf('53', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         ((r2_hidden @ X1 @ X0)
% 0.81/0.98          | ((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.81/0.98      inference('sup-', [status(thm)], ['49', '52'])).
% 0.81/0.98  thf('54', plain,
% 0.81/0.98      (![X23 : $i, X24 : $i]:
% 0.81/0.98         ((k4_xboole_0 @ X23 @ X24)
% 0.81/0.98           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.81/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.81/0.98  thf('55', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.81/0.98            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.81/0.98          | (r2_hidden @ X0 @ X1))),
% 0.81/0.98      inference('sup+', [status(thm)], ['53', '54'])).
% 0.81/0.98  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.81/0.98      inference('sup+', [status(thm)], ['37', '38'])).
% 0.81/0.98  thf('57', plain,
% 0.81/0.98      (![X0 : $i, X1 : $i]:
% 0.81/0.98         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.81/0.98          | (r2_hidden @ X0 @ X1))),
% 0.81/0.98      inference('demod', [status(thm)], ['55', '56'])).
% 0.81/0.98  thf('58', plain,
% 0.81/0.98      (((sk_B)
% 0.81/0.98         != (k2_yellow19 @ sk_A @ 
% 0.81/0.98             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf('59', plain,
% 0.81/0.98      ((m1_subset_1 @ sk_B @ 
% 0.81/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf(d2_yellow_1, axiom,
% 0.81/0.98    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.81/0.98  thf('60', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('61', plain,
% 0.81/0.98      ((m1_subset_1 @ sk_B @ 
% 0.81/0.98        (k1_zfmisc_1 @ 
% 0.81/0.98         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.81/0.98      inference('demod', [status(thm)], ['59', '60'])).
% 0.81/0.98  thf(t14_yellow19, axiom,
% 0.81/0.98    (![A:$i]:
% 0.81/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.81/0.98       ( ![B:$i]:
% 0.81/0.98         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/0.98             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.81/0.98             ( m1_subset_1 @
% 0.81/0.98               B @ 
% 0.81/0.98               ( k1_zfmisc_1 @
% 0.81/0.98                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.81/0.98           ( ( k7_subset_1 @
% 0.81/0.98               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.81/0.98               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.81/0.98             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.81/0.98  thf('62', plain,
% 0.81/0.98      (![X40 : $i, X41 : $i]:
% 0.81/0.98         ((v1_xboole_0 @ X40)
% 0.81/0.98          | ~ (v2_waybel_0 @ X40 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))
% 0.81/0.98          | ~ (v13_waybel_0 @ X40 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))
% 0.81/0.98          | ~ (m1_subset_1 @ X40 @ 
% 0.81/0.98               (k1_zfmisc_1 @ 
% 0.81/0.98                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))))
% 0.81/0.98          | ((k7_subset_1 @ 
% 0.81/0.98              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X41))) @ X40 @ 
% 0.81/0.98              (k1_tarski @ k1_xboole_0))
% 0.81/0.98              = (k2_yellow19 @ X41 @ 
% 0.81/0.98                 (k3_yellow19 @ X41 @ (k2_struct_0 @ X41) @ X40)))
% 0.81/0.98          | ~ (l1_struct_0 @ X41)
% 0.81/0.98          | (v2_struct_0 @ X41))),
% 0.81/0.98      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.81/0.98  thf('63', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('64', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('65', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('66', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('67', plain,
% 0.81/0.98      (![X40 : $i, X41 : $i]:
% 0.81/0.98         ((v1_xboole_0 @ X40)
% 0.81/0.98          | ~ (v2_waybel_0 @ X40 @ 
% 0.81/0.98               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))
% 0.81/0.98          | ~ (v13_waybel_0 @ X40 @ 
% 0.81/0.98               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))
% 0.81/0.98          | ~ (m1_subset_1 @ X40 @ 
% 0.81/0.98               (k1_zfmisc_1 @ 
% 0.81/0.98                (u1_struct_0 @ 
% 0.81/0.98                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))))
% 0.81/0.98          | ((k7_subset_1 @ 
% 0.81/0.98              (u1_struct_0 @ 
% 0.81/0.98               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41)))) @ 
% 0.81/0.98              X40 @ (k1_tarski @ k1_xboole_0))
% 0.81/0.98              = (k2_yellow19 @ X41 @ 
% 0.81/0.98                 (k3_yellow19 @ X41 @ (k2_struct_0 @ X41) @ X40)))
% 0.81/0.98          | ~ (l1_struct_0 @ X41)
% 0.81/0.98          | (v2_struct_0 @ X41))),
% 0.81/0.98      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.81/0.98  thf('68', plain,
% 0.81/0.98      (((v2_struct_0 @ sk_A)
% 0.81/0.98        | ~ (l1_struct_0 @ sk_A)
% 0.81/0.98        | ((k7_subset_1 @ 
% 0.81/0.98            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.81/0.98            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.81/0.98            = (k2_yellow19 @ sk_A @ 
% 0.81/0.98               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.81/0.98        | ~ (v13_waybel_0 @ sk_B @ 
% 0.81/0.98             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.81/0.98        | ~ (v2_waybel_0 @ sk_B @ 
% 0.81/0.98             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.81/0.98        | (v1_xboole_0 @ sk_B))),
% 0.81/0.98      inference('sup-', [status(thm)], ['61', '67'])).
% 0.81/0.98  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf('70', plain,
% 0.81/0.98      ((m1_subset_1 @ sk_B @ 
% 0.81/0.98        (k1_zfmisc_1 @ 
% 0.81/0.98         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.81/0.98      inference('demod', [status(thm)], ['59', '60'])).
% 0.81/0.98  thf(redefinition_k7_subset_1, axiom,
% 0.81/0.98    (![A:$i,B:$i,C:$i]:
% 0.81/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/0.98       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.81/0.98  thf('71', plain,
% 0.81/0.98      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.81/0.98         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.81/0.98          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 0.81/0.98      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.81/0.98  thf('72', plain,
% 0.81/0.98      (![X0 : $i]:
% 0.81/0.98         ((k7_subset_1 @ 
% 0.81/0.98           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.81/0.98           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.81/0.98      inference('sup-', [status(thm)], ['70', '71'])).
% 0.81/0.98  thf('73', plain,
% 0.81/0.98      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf('74', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('75', plain,
% 0.81/0.98      ((v13_waybel_0 @ sk_B @ 
% 0.81/0.98        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.81/0.98      inference('demod', [status(thm)], ['73', '74'])).
% 0.81/0.98  thf('76', plain,
% 0.81/0.98      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.81/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.98  thf('77', plain,
% 0.81/0.98      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.98      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.98  thf('78', plain,
% 0.81/0.98      ((v2_waybel_0 @ sk_B @ 
% 0.81/0.98        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.81/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.81/0.99  thf('79', plain,
% 0.81/0.99      (((v2_struct_0 @ sk_A)
% 0.81/0.99        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.81/0.99            = (k2_yellow19 @ sk_A @ 
% 0.81/0.99               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.81/0.99        | (v1_xboole_0 @ sk_B))),
% 0.81/0.99      inference('demod', [status(thm)], ['68', '69', '72', '75', '78'])).
% 0.81/0.99  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('81', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_B)
% 0.81/0.99        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.81/0.99            = (k2_yellow19 @ sk_A @ 
% 0.81/0.99               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.81/0.99      inference('clc', [status(thm)], ['79', '80'])).
% 0.81/0.99  thf('82', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('83', plain,
% 0.81/0.99      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.81/0.99         = (k2_yellow19 @ sk_A @ 
% 0.81/0.99            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.81/0.99      inference('clc', [status(thm)], ['81', '82'])).
% 0.81/0.99  thf('84', plain,
% 0.81/0.99      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.81/0.99      inference('demod', [status(thm)], ['58', '83'])).
% 0.81/0.99  thf('85', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['57', '84'])).
% 0.81/0.99  thf('86', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.81/0.99      inference('simplify', [status(thm)], ['85'])).
% 0.81/0.99  thf('87', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_B @ 
% 0.81/0.99        (k1_zfmisc_1 @ 
% 0.81/0.99         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.81/0.99      inference('demod', [status(thm)], ['59', '60'])).
% 0.81/0.99  thf(t2_yellow19, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99       ( ![B:$i]:
% 0.81/0.99         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/0.99             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.81/0.99             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.81/0.99             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.81/0.99             ( m1_subset_1 @
% 0.81/0.99               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.81/0.99           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.81/0.99  thf('88', plain,
% 0.81/0.99      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X42)
% 0.81/0.99          | ~ (v1_subset_1 @ X42 @ (u1_struct_0 @ (k3_yellow_1 @ X43)))
% 0.81/0.99          | ~ (v2_waybel_0 @ X42 @ (k3_yellow_1 @ X43))
% 0.81/0.99          | ~ (v13_waybel_0 @ X42 @ (k3_yellow_1 @ X43))
% 0.81/0.99          | ~ (m1_subset_1 @ X42 @ 
% 0.81/0.99               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X43))))
% 0.81/0.99          | ~ (r2_hidden @ X44 @ X42)
% 0.81/0.99          | ~ (v1_xboole_0 @ X44)
% 0.81/0.99          | (v1_xboole_0 @ X43))),
% 0.81/0.99      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.81/0.99  thf('89', plain,
% 0.81/0.99      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.99  thf('90', plain,
% 0.81/0.99      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.99  thf('91', plain,
% 0.81/0.99      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.99  thf('92', plain,
% 0.81/0.99      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.99  thf('93', plain,
% 0.81/0.99      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X42)
% 0.81/0.99          | ~ (v1_subset_1 @ X42 @ 
% 0.81/0.99               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X43))))
% 0.81/0.99          | ~ (v2_waybel_0 @ X42 @ (k3_lattice3 @ (k1_lattice3 @ X43)))
% 0.81/0.99          | ~ (v13_waybel_0 @ X42 @ (k3_lattice3 @ (k1_lattice3 @ X43)))
% 0.81/0.99          | ~ (m1_subset_1 @ X42 @ 
% 0.81/0.99               (k1_zfmisc_1 @ 
% 0.81/0.99                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X43)))))
% 0.81/0.99          | ~ (r2_hidden @ X44 @ X42)
% 0.81/0.99          | ~ (v1_xboole_0 @ X44)
% 0.81/0.99          | (v1_xboole_0 @ X43))),
% 0.81/0.99      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.81/0.99  thf('94', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.81/0.99          | ~ (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (r2_hidden @ X0 @ sk_B)
% 0.81/0.99          | ~ (v13_waybel_0 @ sk_B @ 
% 0.81/0.99               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.81/0.99          | ~ (v2_waybel_0 @ sk_B @ 
% 0.81/0.99               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.81/0.99          | ~ (v1_subset_1 @ sk_B @ 
% 0.81/0.99               (u1_struct_0 @ 
% 0.81/0.99                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.81/0.99          | (v1_xboole_0 @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['87', '93'])).
% 0.81/0.99  thf('95', plain,
% 0.81/0.99      ((v13_waybel_0 @ sk_B @ 
% 0.81/0.99        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.81/0.99      inference('demod', [status(thm)], ['73', '74'])).
% 0.81/0.99  thf('96', plain,
% 0.81/0.99      ((v2_waybel_0 @ sk_B @ 
% 0.81/0.99        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.81/0.99      inference('demod', [status(thm)], ['76', '77'])).
% 0.81/0.99  thf('97', plain,
% 0.81/0.99      ((v1_subset_1 @ sk_B @ 
% 0.81/0.99        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('98', plain,
% 0.81/0.99      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.81/0.99  thf('99', plain,
% 0.81/0.99      ((v1_subset_1 @ sk_B @ 
% 0.81/0.99        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.81/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.81/0.99  thf('100', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.81/0.99          | ~ (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (r2_hidden @ X0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_B))),
% 0.81/0.99      inference('demod', [status(thm)], ['94', '95', '96', '99'])).
% 0.81/0.99  thf('101', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_B)
% 0.81/0.99        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.81/0.99        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['86', '100'])).
% 0.81/0.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.81/0.99  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/0.99  thf('103', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.81/0.99      inference('demod', [status(thm)], ['101', '102'])).
% 0.81/0.99  thf('104', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('105', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.81/0.99      inference('clc', [status(thm)], ['103', '104'])).
% 0.81/0.99  thf('106', plain,
% 0.81/0.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.81/0.99      inference('sup+', [status(thm)], ['1', '105'])).
% 0.81/0.99  thf('107', plain, ((l1_struct_0 @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('108', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.81/0.99      inference('demod', [status(thm)], ['106', '107'])).
% 0.81/0.99  thf(fc2_struct_0, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.81/0.99       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.81/0.99  thf('109', plain,
% 0.81/0.99      (![X38 : $i]:
% 0.81/0.99         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.81/0.99          | ~ (l1_struct_0 @ X38)
% 0.81/0.99          | (v2_struct_0 @ X38))),
% 0.81/0.99      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.81/0.99  thf('110', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['108', '109'])).
% 0.81/0.99  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('112', plain, ((v2_struct_0 @ sk_A)),
% 0.81/0.99      inference('demod', [status(thm)], ['110', '111'])).
% 0.81/0.99  thf('113', plain, ($false), inference('demod', [status(thm)], ['0', '112'])).
% 0.81/0.99  
% 0.81/0.99  % SZS output end Refutation
% 0.81/0.99  
% 0.81/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
