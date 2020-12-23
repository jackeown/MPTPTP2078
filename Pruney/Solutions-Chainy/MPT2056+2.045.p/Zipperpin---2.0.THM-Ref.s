%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0nW8PjqGwS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:46 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 185 expanded)
%              Number of leaves         :   40 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  981 (2291 expanded)
%              Number of equality atoms :   48 (  99 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) @ X20 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) @ X20 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','35','38','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','46'])).

thf('48',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','47'])).

thf('49',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_yellow_1 @ X23 ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_yellow_1 @ X23 ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_yellow_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X23 ) ) ) )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('56',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ) )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('63',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('64',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','76'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0nW8PjqGwS
% 0.16/0.40  % Computer   : n024.cluster.edu
% 0.16/0.40  % Model      : x86_64 x86_64
% 0.16/0.40  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.40  % Memory     : 8042.1875MB
% 0.16/0.40  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.40  % CPULimit   : 60
% 0.16/0.40  % DateTime   : Tue Dec  1 11:27:21 EST 2020
% 0.16/0.40  % CPUTime    : 
% 0.16/0.40  % Running portfolio for 600 s
% 0.16/0.40  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.40  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.26/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.56  % Solved by: fo/fo7.sh
% 0.26/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.56  % done 76 iterations in 0.040s
% 0.26/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.56  % SZS output start Refutation
% 0.26/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.26/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.26/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.26/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.26/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.56  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.26/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.56  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.26/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.26/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.26/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.26/0.56  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.26/0.56  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.26/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.26/0.56  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.26/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.26/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.26/0.56  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.26/0.56  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.26/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.26/0.56  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.26/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.26/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.26/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.26/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.26/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.26/0.56  thf(t15_yellow19, conjecture,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56             ( v1_subset_1 @
% 0.26/0.56               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.26/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56             ( m1_subset_1 @
% 0.26/0.56               B @ 
% 0.26/0.56               ( k1_zfmisc_1 @
% 0.26/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.26/0.56           ( ( B ) =
% 0.26/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.26/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.56    (~( ![A:$i]:
% 0.26/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.26/0.56          ( ![B:$i]:
% 0.26/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56                ( v1_subset_1 @
% 0.26/0.56                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.26/0.56                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56                ( m1_subset_1 @
% 0.26/0.56                  B @ 
% 0.26/0.56                  ( k1_zfmisc_1 @
% 0.26/0.56                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.26/0.56              ( ( B ) =
% 0.26/0.56                ( k2_yellow19 @
% 0.26/0.56                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.26/0.56    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.26/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf(t3_xboole_0, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.26/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.26/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.26/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.26/0.56  thf('1', plain,
% 0.26/0.56      (![X3 : $i, X4 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.26/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.26/0.56  thf(t17_zfmisc_1, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( ( A ) != ( B ) ) =>
% 0.26/0.56       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.26/0.56  thf('2', plain,
% 0.26/0.56      (![X13 : $i, X14 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14))
% 0.26/0.56          | ((X13) = (X14)))),
% 0.26/0.56      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.26/0.56  thf(l24_zfmisc_1, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.26/0.56  thf('3', plain,
% 0.26/0.56      (![X11 : $i, X12 : $i]:
% 0.26/0.56         (~ (r1_xboole_0 @ (k1_tarski @ X11) @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.26/0.56      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.26/0.56  thf('4', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.26/0.56  thf('5', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.26/0.56          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.26/0.56  thf('6', plain,
% 0.26/0.56      (![X3 : $i, X4 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.26/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.26/0.56  thf('7', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         ((r2_hidden @ X0 @ X1)
% 0.26/0.56          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.26/0.56          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.26/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.26/0.56  thf('8', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.26/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.26/0.56  thf(d7_xboole_0, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.26/0.56       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.26/0.56  thf('9', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.26/0.56  thf('10', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         ((r2_hidden @ X0 @ X1)
% 0.26/0.56          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.26/0.56  thf(t100_xboole_1, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.26/0.56  thf('11', plain,
% 0.26/0.56      (![X7 : $i, X8 : $i]:
% 0.26/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.26/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.26/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.26/0.56  thf('12', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.26/0.56            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.26/0.56          | (r2_hidden @ X0 @ X1))),
% 0.26/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.26/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.26/0.56  thf('13', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.26/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.26/0.56  thf('14', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.26/0.56  thf('15', plain,
% 0.26/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.26/0.56  thf('16', plain,
% 0.26/0.56      (![X7 : $i, X8 : $i]:
% 0.26/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.26/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.26/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.26/0.56  thf('17', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.26/0.56      inference('sup+', [status(thm)], ['15', '16'])).
% 0.26/0.56  thf(t3_boole, axiom,
% 0.26/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.26/0.56  thf('18', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.26/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.26/0.56  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.26/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.26/0.56  thf('20', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.26/0.56          | (r2_hidden @ X0 @ X1))),
% 0.26/0.56      inference('demod', [status(thm)], ['12', '19'])).
% 0.26/0.56  thf('21', plain,
% 0.26/0.56      (((sk_B)
% 0.26/0.56         != (k2_yellow19 @ sk_A @ 
% 0.26/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('22', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B @ 
% 0.26/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf(d2_yellow_1, axiom,
% 0.26/0.56    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.26/0.56  thf('23', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('24', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B @ 
% 0.26/0.56        (k1_zfmisc_1 @ 
% 0.26/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.26/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.26/0.56  thf(t14_yellow19, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.26/0.56             ( m1_subset_1 @
% 0.26/0.56               B @ 
% 0.26/0.56               ( k1_zfmisc_1 @
% 0.26/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.26/0.56           ( ( k7_subset_1 @
% 0.26/0.56               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.26/0.56               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.26/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.26/0.56  thf('25', plain,
% 0.26/0.56      (![X20 : $i, X21 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X20)
% 0.26/0.56          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.26/0.56          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.26/0.56          | ~ (m1_subset_1 @ X20 @ 
% 0.26/0.56               (k1_zfmisc_1 @ 
% 0.26/0.56                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))))
% 0.26/0.56          | ((k7_subset_1 @ 
% 0.26/0.56              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21))) @ X20 @ 
% 0.26/0.56              (k1_tarski @ k1_xboole_0))
% 0.26/0.56              = (k2_yellow19 @ X21 @ 
% 0.26/0.56                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.26/0.56          | ~ (l1_struct_0 @ X21)
% 0.26/0.56          | (v2_struct_0 @ X21))),
% 0.26/0.56      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.26/0.56  thf('26', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('27', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('28', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('29', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('30', plain,
% 0.26/0.56      (![X20 : $i, X21 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X20)
% 0.26/0.56          | ~ (v2_waybel_0 @ X20 @ 
% 0.26/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.26/0.56          | ~ (v13_waybel_0 @ X20 @ 
% 0.26/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.26/0.56          | ~ (m1_subset_1 @ X20 @ 
% 0.26/0.56               (k1_zfmisc_1 @ 
% 0.26/0.56                (u1_struct_0 @ 
% 0.26/0.56                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))))
% 0.26/0.56          | ((k7_subset_1 @ 
% 0.26/0.56              (u1_struct_0 @ 
% 0.26/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21)))) @ 
% 0.26/0.56              X20 @ (k1_tarski @ k1_xboole_0))
% 0.26/0.56              = (k2_yellow19 @ X21 @ 
% 0.26/0.56                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.26/0.56          | ~ (l1_struct_0 @ X21)
% 0.26/0.56          | (v2_struct_0 @ X21))),
% 0.26/0.56      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.26/0.56  thf('31', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.26/0.56        | ((k7_subset_1 @ 
% 0.26/0.56            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.26/0.56            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.26/0.56            = (k2_yellow19 @ sk_A @ 
% 0.26/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.26/0.56        | ~ (v13_waybel_0 @ sk_B @ 
% 0.26/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.26/0.56        | ~ (v2_waybel_0 @ sk_B @ 
% 0.26/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.26/0.56        | (v1_xboole_0 @ sk_B))),
% 0.26/0.56      inference('sup-', [status(thm)], ['24', '30'])).
% 0.26/0.56  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('33', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B @ 
% 0.26/0.56        (k1_zfmisc_1 @ 
% 0.26/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.26/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.26/0.56  thf(redefinition_k7_subset_1, axiom,
% 0.26/0.56    (![A:$i,B:$i,C:$i]:
% 0.26/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.26/0.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.26/0.56  thf('34', plain,
% 0.26/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.26/0.56          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.26/0.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.26/0.56  thf('35', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((k7_subset_1 @ 
% 0.26/0.56           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.26/0.56           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.26/0.56  thf('36', plain,
% 0.26/0.56      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('37', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('38', plain,
% 0.26/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.26/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.26/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.26/0.56  thf('39', plain,
% 0.26/0.56      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('40', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('41', plain,
% 0.26/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.26/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.26/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.26/0.56  thf('42', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.26/0.56            = (k2_yellow19 @ sk_A @ 
% 0.26/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.26/0.56        | (v1_xboole_0 @ sk_B))),
% 0.26/0.56      inference('demod', [status(thm)], ['31', '32', '35', '38', '41'])).
% 0.26/0.56  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('44', plain,
% 0.26/0.56      (((v1_xboole_0 @ sk_B)
% 0.26/0.56        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.26/0.56            = (k2_yellow19 @ sk_A @ 
% 0.26/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.26/0.56      inference('clc', [status(thm)], ['42', '43'])).
% 0.26/0.56  thf('45', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('46', plain,
% 0.26/0.56      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.26/0.56         = (k2_yellow19 @ sk_A @ 
% 0.26/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.26/0.56      inference('clc', [status(thm)], ['44', '45'])).
% 0.26/0.56  thf('47', plain,
% 0.26/0.56      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.26/0.56      inference('demod', [status(thm)], ['21', '46'])).
% 0.26/0.56  thf('48', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.26/0.56      inference('sup-', [status(thm)], ['20', '47'])).
% 0.26/0.56  thf('49', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.26/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.26/0.56  thf('50', plain,
% 0.26/0.56      (![X3 : $i, X4 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.26/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.26/0.56  thf('51', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.26/0.56  thf('52', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.26/0.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.26/0.56  thf('53', plain,
% 0.26/0.56      (![X3 : $i, X4 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.26/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.26/0.56  thf('54', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B @ 
% 0.26/0.56        (k1_zfmisc_1 @ 
% 0.26/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.26/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.26/0.56  thf(t2_yellow19, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.26/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.26/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.26/0.56             ( m1_subset_1 @
% 0.26/0.56               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.26/0.56           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.26/0.56  thf('55', plain,
% 0.26/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X22)
% 0.26/0.56          | ~ (v1_subset_1 @ X22 @ (u1_struct_0 @ (k3_yellow_1 @ X23)))
% 0.26/0.56          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ X23))
% 0.26/0.56          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ X23))
% 0.26/0.56          | ~ (m1_subset_1 @ X22 @ 
% 0.26/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X23))))
% 0.26/0.56          | ~ (r2_hidden @ X24 @ X22)
% 0.26/0.56          | ~ (v1_xboole_0 @ X24)
% 0.26/0.56          | (v1_xboole_0 @ X23))),
% 0.26/0.56      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.26/0.56  thf('56', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('57', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('58', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('59', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('60', plain,
% 0.26/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X22)
% 0.26/0.56          | ~ (v1_subset_1 @ X22 @ 
% 0.26/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X23))))
% 0.26/0.56          | ~ (v2_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X23)))
% 0.26/0.56          | ~ (v13_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X23)))
% 0.26/0.56          | ~ (m1_subset_1 @ X22 @ 
% 0.26/0.56               (k1_zfmisc_1 @ 
% 0.26/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X23)))))
% 0.26/0.56          | ~ (r2_hidden @ X24 @ X22)
% 0.26/0.56          | ~ (v1_xboole_0 @ X24)
% 0.26/0.56          | (v1_xboole_0 @ X23))),
% 0.26/0.56      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.26/0.56  thf('61', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.26/0.56          | ~ (v1_xboole_0 @ X0)
% 0.26/0.56          | ~ (r2_hidden @ X0 @ sk_B)
% 0.26/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.26/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.26/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.26/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.26/0.56          | ~ (v1_subset_1 @ sk_B @ 
% 0.26/0.56               (u1_struct_0 @ 
% 0.26/0.56                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.26/0.56          | (v1_xboole_0 @ sk_B))),
% 0.26/0.56      inference('sup-', [status(thm)], ['54', '60'])).
% 0.26/0.56  thf('62', plain,
% 0.26/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.26/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.26/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.26/0.56  thf('63', plain,
% 0.26/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.26/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.26/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.26/0.56  thf('64', plain,
% 0.26/0.56      ((v1_subset_1 @ sk_B @ 
% 0.26/0.56        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('65', plain,
% 0.26/0.56      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.26/0.56  thf('66', plain,
% 0.26/0.56      ((v1_subset_1 @ sk_B @ 
% 0.26/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.26/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.26/0.56  thf('67', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.26/0.56          | ~ (v1_xboole_0 @ X0)
% 0.26/0.56          | ~ (r2_hidden @ X0 @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ sk_B))),
% 0.26/0.56      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.26/0.56  thf('68', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((r1_xboole_0 @ X0 @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ sk_B)
% 0.26/0.56          | ~ (v1_xboole_0 @ (sk_C @ sk_B @ X0))
% 0.26/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['53', '67'])).
% 0.26/0.56  thf('69', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         (~ (v1_xboole_0 @ X0)
% 0.26/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.26/0.56          | (v1_xboole_0 @ sk_B)
% 0.26/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B))),
% 0.26/0.56      inference('sup-', [status(thm)], ['52', '68'])).
% 0.26/0.56  thf('70', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.26/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.26/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.26/0.56      inference('simplify', [status(thm)], ['69'])).
% 0.26/0.56  thf(fc5_struct_0, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.26/0.56       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.26/0.56  thf('71', plain,
% 0.26/0.56      (![X18 : $i]:
% 0.26/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X18))
% 0.26/0.56          | ~ (l1_struct_0 @ X18)
% 0.26/0.56          | (v2_struct_0 @ X18))),
% 0.26/0.56      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.26/0.56  thf('72', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         (~ (v1_xboole_0 @ X0)
% 0.26/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ sk_B)
% 0.26/0.56          | (v2_struct_0 @ sk_A)
% 0.26/0.56          | ~ (l1_struct_0 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.26/0.56  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('74', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         (~ (v1_xboole_0 @ X0)
% 0.26/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.26/0.56          | (v1_xboole_0 @ sk_B)
% 0.26/0.56          | (v2_struct_0 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.26/0.56  thf('75', plain,
% 0.26/0.56      (![X11 : $i, X12 : $i]:
% 0.26/0.56         (~ (r1_xboole_0 @ (k1_tarski @ X11) @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.26/0.56      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.26/0.56  thf('76', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v2_struct_0 @ sk_A)
% 0.26/0.56          | (v1_xboole_0 @ sk_B)
% 0.26/0.56          | ~ (v1_xboole_0 @ X0)
% 0.26/0.56          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.26/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.26/0.56  thf('77', plain,
% 0.26/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.26/0.56        | (v1_xboole_0 @ sk_B)
% 0.26/0.56        | (v2_struct_0 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['49', '76'])).
% 0.26/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.26/0.56  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.26/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.26/0.56  thf('79', plain, (((v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['77', '78'])).
% 0.26/0.56  thf('80', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('81', plain, ((v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('clc', [status(thm)], ['79', '80'])).
% 0.26/0.56  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 0.26/0.56  
% 0.26/0.56  % SZS output end Refutation
% 0.26/0.56  
% 0.26/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
