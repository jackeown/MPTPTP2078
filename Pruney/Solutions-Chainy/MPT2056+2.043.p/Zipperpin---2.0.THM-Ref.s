%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AuCXcsfvo2

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 159 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  808 (2122 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) @ X17 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) @ X17 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','26','29','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','37'])).

thf('39',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','38'])).

thf('40',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('43',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('50',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('51',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','54'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AuCXcsfvo2
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 61 iterations in 0.039s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.53  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.53  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(t15_yellow19, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53             ( v1_subset_1 @
% 0.20/0.53               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53             ( m1_subset_1 @
% 0.20/0.53               B @ 
% 0.20/0.53               ( k1_zfmisc_1 @
% 0.20/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.53           ( ( B ) =
% 0.20/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53                ( v1_subset_1 @
% 0.20/0.53                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.53                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53                ( m1_subset_1 @
% 0.20/0.53                  B @ 
% 0.20/0.53                  ( k1_zfmisc_1 @
% 0.20/0.53                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.53              ( ( B ) =
% 0.20/0.53                ( k2_yellow19 @
% 0.20/0.53                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.20/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X14 : $i]:
% 0.20/0.53         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.53  thf(l27_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ (k1_tarski @ X9) @ X10) | (r2_hidden @ X9 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.53  thf(t3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.53          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.53          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.53  thf(t83_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ X1)
% 0.20/0.53          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((sk_B)
% 0.20/0.53         != (k2_yellow19 @ sk_A @ 
% 0.20/0.53             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_yellow_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t14_yellow19, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.53             ( m1_subset_1 @
% 0.20/0.53               B @ 
% 0.20/0.53               ( k1_zfmisc_1 @
% 0.20/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.53           ( ( k7_subset_1 @
% 0.20/0.53               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.20/0.53               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.20/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X17)
% 0.20/0.53          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.20/0.53          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))))
% 0.20/0.53          | ((k7_subset_1 @ 
% 0.20/0.53              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18))) @ X17 @ 
% 0.20/0.53              (k1_tarski @ k1_xboole_0))
% 0.20/0.53              = (k2_yellow19 @ X18 @ 
% 0.20/0.53                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.20/0.53          | ~ (l1_struct_0 @ X18)
% 0.20/0.53          | (v2_struct_0 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X17)
% 0.20/0.53          | ~ (v2_waybel_0 @ X17 @ 
% 0.20/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.20/0.53          | ~ (v13_waybel_0 @ X17 @ 
% 0.20/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (u1_struct_0 @ 
% 0.20/0.53                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))))
% 0.20/0.53          | ((k7_subset_1 @ 
% 0.20/0.53              (u1_struct_0 @ 
% 0.20/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18)))) @ 
% 0.20/0.53              X17 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.53              = (k2_yellow19 @ X18 @ 
% 0.20/0.53                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.20/0.53          | ~ (l1_struct_0 @ X18)
% 0.20/0.53          | (v2_struct_0 @ X18))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.53        | ((k7_subset_1 @ 
% 0.20/0.53            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.53            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.20/0.53            = (k2_yellow19 @ sk_A @ 
% 0.20/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.53        | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.53        | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.53        | (v1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.53  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.53          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ 
% 0.20/0.53           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.53           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.20/0.53            = (k2_yellow19 @ sk_A @ 
% 0.20/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.53        | (v1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '26', '29', '32'])).
% 0.20/0.53  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B)
% 0.20/0.53        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.20/0.53            = (k2_yellow19 @ sk_A @ 
% 0.20/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.53      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.20/0.53         = (k2_yellow19 @ sk_A @ 
% 0.20/0.53            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '37'])).
% 0.20/0.53  thf('39', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '38'])).
% 0.20/0.53  thf('40', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t2_yellow19, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.53             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.53             ( m1_subset_1 @
% 0.20/0.53               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.53           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X19)
% 0.20/0.53          | ~ (v1_subset_1 @ X19 @ (u1_struct_0 @ (k3_yellow_1 @ X20)))
% 0.20/0.53          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ X20))
% 0.20/0.53          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X20))))
% 0.20/0.53          | ~ (r2_hidden @ X21 @ X19)
% 0.20/0.53          | ~ (v1_xboole_0 @ X21)
% 0.20/0.53          | (v1_xboole_0 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X19)
% 0.20/0.53          | ~ (v1_subset_1 @ X19 @ 
% 0.20/0.53               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20))))
% 0.20/0.53          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 0.20/0.53          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20)))))
% 0.20/0.53          | ~ (r2_hidden @ X21 @ X19)
% 0.20/0.53          | ~ (v1_xboole_0 @ X21)
% 0.20/0.53          | (v1_xboole_0 @ X20))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.53          | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.53          | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.53          | ~ (v1_subset_1 @ sk_B @ 
% 0.20/0.53               (u1_struct_0 @ 
% 0.20/0.53                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.53          | (v1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((v1_subset_1 @ sk_B @ 
% 0.20/0.53        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((v1_subset_1 @ sk_B @ 
% 0.20/0.53        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.53          | (v1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49', '50', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B)
% 0.20/0.53        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '54'])).
% 0.20/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.53  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['1', '59'])).
% 0.20/0.53  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf(fc2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X15 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.20/0.53          | ~ (l1_struct_0 @ X15)
% 0.20/0.53          | (v2_struct_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('64', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
