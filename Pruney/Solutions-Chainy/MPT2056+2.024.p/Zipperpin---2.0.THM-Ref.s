%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NOD3zT8oq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 238 expanded)
%              Number of leaves         :   40 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          : 1191 (2784 expanded)
%              Number of equality atoms :   53 ( 122 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X22 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(clc,[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('28',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('31',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37','40','43','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','51'])).

thf('53',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','52'])).

thf('54',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(clc,[status(thm)],['8','12'])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ X31 ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('66',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('67',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['64','65','66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('79',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X22 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ X0 )
        = X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ X1 )
        = X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('88',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7NOD3zT8oq
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 199 iterations in 0.081s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.19/0.53  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.53  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.53  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.53  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(t15_yellow19, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.53             ( v1_subset_1 @
% 0.19/0.53               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53             ( m1_subset_1 @
% 0.19/0.53               B @ 
% 0.19/0.53               ( k1_zfmisc_1 @
% 0.19/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.53           ( ( B ) =
% 0.19/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.53                ( v1_subset_1 @
% 0.19/0.53                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.53                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53                ( m1_subset_1 @
% 0.19/0.53                  B @ 
% 0.19/0.53                  ( k1_zfmisc_1 @
% 0.19/0.53                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.53              ( ( B ) =
% 0.19/0.53                ( k2_yellow19 @
% 0.19/0.53                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.19/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d10_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.53  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.19/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.53  thf(l32_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X10 : $i, X12 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.19/0.53          | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.53  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf(t3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf(t64_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.19/0.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.19/0.53         ((r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X22)))
% 0.19/0.53          | ((X19) = (X22))
% 0.19/0.53          | ~ (r2_hidden @ X19 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.53          | ((sk_C @ X1 @ X0) = (X2))
% 0.19/0.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.19/0.53             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ k1_xboole_0)
% 0.19/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['4', '7'])).
% 0.19/0.53  thf(t4_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.53         (((X19) != (X21))
% 0.19/0.53          | ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21))))),
% 0.19/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X20 : $i, X21 : $i]:
% 0.19/0.53         ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.53  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['9', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.53      inference('clc', [status(thm)], ['8', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ X0 @ X1)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X5 @ X3)
% 0.19/0.53          | ~ (r2_hidden @ X5 @ X6)
% 0.19/0.53          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.53          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['16', '22'])).
% 0.19/0.53  thf(t83_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.19/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ X0 @ X1)
% 0.19/0.53          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((sk_B_1)
% 0.19/0.53         != (k2_yellow19 @ sk_A @ 
% 0.19/0.53             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d2_yellow_1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (k1_zfmisc_1 @ 
% 0.19/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf(t14_yellow19, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.53             ( m1_subset_1 @
% 0.19/0.53               B @ 
% 0.19/0.53               ( k1_zfmisc_1 @
% 0.19/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.53           ( ( k7_subset_1 @
% 0.19/0.53               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.19/0.53               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.19/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X28)
% 0.19/0.53          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.19/0.53          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.19/0.53          | ~ (m1_subset_1 @ X28 @ 
% 0.19/0.53               (k1_zfmisc_1 @ 
% 0.19/0.53                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.19/0.53          | ((k7_subset_1 @ 
% 0.19/0.53              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))) @ X28 @ 
% 0.19/0.53              (k1_tarski @ k1_xboole_0))
% 0.19/0.53              = (k2_yellow19 @ X29 @ 
% 0.19/0.53                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.19/0.53          | ~ (l1_struct_0 @ X29)
% 0.19/0.53          | (v2_struct_0 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X28)
% 0.19/0.53          | ~ (v2_waybel_0 @ X28 @ 
% 0.19/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.19/0.53          | ~ (v13_waybel_0 @ X28 @ 
% 0.19/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.19/0.53          | ~ (m1_subset_1 @ X28 @ 
% 0.19/0.53               (k1_zfmisc_1 @ 
% 0.19/0.53                (u1_struct_0 @ 
% 0.19/0.53                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.19/0.53          | ((k7_subset_1 @ 
% 0.19/0.53              (u1_struct_0 @ 
% 0.19/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))) @ 
% 0.19/0.53              X28 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.53              = (k2_yellow19 @ X29 @ 
% 0.19/0.53                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.19/0.53          | ~ (l1_struct_0 @ X29)
% 0.19/0.53          | (v2_struct_0 @ X29))),
% 0.19/0.53      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.53        | ((k7_subset_1 @ 
% 0.19/0.53            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.19/0.53            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.53            = (k2_yellow19 @ sk_A @ 
% 0.19/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.19/0.53        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.53        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['29', '35'])).
% 0.19/0.53  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (k1_zfmisc_1 @ 
% 0.19/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.19/0.53          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k7_subset_1 @ 
% 0.19/0.53           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.19/0.53           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      ((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      ((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.53            = (k2_yellow19 @ sk_A @ 
% 0.19/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['36', '37', '40', '43', '46'])).
% 0.19/0.53  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.53            = (k2_yellow19 @ sk_A @ 
% 0.19/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.19/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.53  thf('50', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.53         = (k2_yellow19 @ sk_A @ 
% 0.19/0.53            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.53      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['26', '51'])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['25', '52'])).
% 0.19/0.53  thf('54', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.53      inference('clc', [status(thm)], ['8', '12'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (k1_zfmisc_1 @ 
% 0.19/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf(t2_yellow19, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.53             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.19/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.53             ( m1_subset_1 @
% 0.19/0.53               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.19/0.53           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X30)
% 0.19/0.53          | ~ (v1_subset_1 @ X30 @ (u1_struct_0 @ (k3_yellow_1 @ X31)))
% 0.19/0.53          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.19/0.53          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X31))))
% 0.19/0.53          | ~ (r2_hidden @ X32 @ X30)
% 0.19/0.53          | ~ (v1_xboole_0 @ X32)
% 0.19/0.53          | (v1_xboole_0 @ X31))),
% 0.19/0.53      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('63', plain,
% 0.19/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X30)
% 0.19/0.53          | ~ (v1_subset_1 @ X30 @ 
% 0.19/0.53               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31))))
% 0.19/0.53          | ~ (v2_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.19/0.53          | ~ (v13_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.53               (k1_zfmisc_1 @ 
% 0.19/0.53                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31)))))
% 0.19/0.53          | ~ (r2_hidden @ X32 @ X30)
% 0.19/0.53          | ~ (v1_xboole_0 @ X32)
% 0.19/0.53          | (v1_xboole_0 @ X31))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.53          | ~ (v1_xboole_0 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.53          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.53          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.53          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.19/0.53               (u1_struct_0 @ 
% 0.19/0.53                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['57', '63'])).
% 0.19/0.53  thf('65', plain,
% 0.19/0.53      ((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      ((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.53  thf('67', plain,
% 0.19/0.53      ((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('68', plain,
% 0.19/0.53      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.53  thf('69', plain,
% 0.19/0.53      ((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.53        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.19/0.53  thf('70', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.53          | ~ (v1_xboole_0 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['64', '65', '66', '69'])).
% 0.19/0.53  thf('71', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.19/0.53          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['56', '70'])).
% 0.19/0.53  thf('72', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['55', '71'])).
% 0.19/0.53  thf('73', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.53          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['72'])).
% 0.19/0.53  thf(fc5_struct_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.19/0.53  thf('74', plain,
% 0.19/0.53      (![X26 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 0.19/0.53          | ~ (l1_struct_0 @ X26)
% 0.19/0.53          | (v2_struct_0 @ X26))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | (v2_struct_0 @ sk_A)
% 0.19/0.53          | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.19/0.53  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('77', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.53  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf(d1_xboole_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.53  thf('79', plain,
% 0.19/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('80', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.19/0.53         ((r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X22)))
% 0.19/0.53          | ((X19) = (X22))
% 0.19/0.53          | ~ (r2_hidden @ X19 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.19/0.53  thf('81', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X0)
% 0.19/0.53          | ((sk_B @ X0) = (X1))
% 0.19/0.53          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.53  thf('82', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('83', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((sk_B @ X1) = (X0))
% 0.19/0.53          | (v1_xboole_0 @ X1)
% 0.19/0.53          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.19/0.53  thf('84', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.19/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['78', '83'])).
% 0.19/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.53  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf('86', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.19/0.53  thf('87', plain,
% 0.19/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('88', plain,
% 0.19/0.53      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X5 @ X3)
% 0.19/0.53          | ~ (r2_hidden @ X5 @ X6)
% 0.19/0.53          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('89', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X0)
% 0.19/0.53          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.19/0.53          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.53  thf('90', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.19/0.53          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['86', '89'])).
% 0.19/0.53  thf('91', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.19/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['90'])).
% 0.19/0.53  thf('92', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('93', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('94', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.53  thf('95', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.19/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.53  thf('96', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.53  thf('97', plain,
% 0.19/0.53      (![X20 : $i, X21 : $i]:
% 0.19/0.53         ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.53  thf('98', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['96', '97'])).
% 0.19/0.53  thf('99', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ X1) | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.19/0.53      inference('clc', [status(thm)], ['91', '98'])).
% 0.19/0.53  thf('100', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53          | ~ (v1_xboole_0 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['77', '99'])).
% 0.19/0.53  thf('101', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['54', '100'])).
% 0.19/0.53  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf('103', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['101', '102'])).
% 0.19/0.53  thf('104', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('clc', [status(thm)], ['103', '104'])).
% 0.19/0.53  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
