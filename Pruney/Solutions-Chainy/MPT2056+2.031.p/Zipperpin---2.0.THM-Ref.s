%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zzm1t1tWou

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 211 expanded)
%              Number of leaves         :   43 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          : 1086 (2704 expanded)
%              Number of equality atoms :   54 ( 114 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('21',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) ) @ X26 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X27 @ ( k3_yellow19 @ X27 @ ( k2_struct_0 @ X27 ) @ X26 ) ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('24',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) ) @ X26 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X27 @ ( k3_yellow19 @ X27 @ ( k2_struct_0 @ X27 ) @ X26 ) ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('39',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30','33','36','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','44'])).

thf('46',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','45'])).

thf('47',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('57',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) ) )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ~ ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('58',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ) )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ~ ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('66',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('71',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('77',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','68','73','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('85',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','90'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zzm1t1tWou
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 142 iterations in 0.079s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.54  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.37/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.54  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.54  thf(t15_yellow19, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.54             ( v1_subset_1 @
% 0.37/0.54               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54             ( m1_subset_1 @
% 0.37/0.54               B @ 
% 0.37/0.54               ( k1_zfmisc_1 @
% 0.37/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.54           ( ( B ) =
% 0.37/0.54             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.54          ( ![B:$i]:
% 0.37/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.54                ( v1_subset_1 @
% 0.37/0.54                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.54                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54                ( m1_subset_1 @
% 0.37/0.54                  B @ 
% 0.37/0.54                  ( k1_zfmisc_1 @
% 0.37/0.54                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.54              ( ( B ) =
% 0.37/0.54                ( k2_yellow19 @
% 0.37/0.54                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.37/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf(t17_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( A ) != ( B ) ) =>
% 0.37/0.54       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.37/0.54          | ((X18) = (X19)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.37/0.54  thf(l24_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X16 : $i, X17 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ (k1_tarski @ X16) @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.37/0.54      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.54          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ X1)
% 0.37/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.54  thf(d7_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]:
% 0.37/0.54         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ X1)
% 0.37/0.54          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf(t100_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X10 : $i, X11 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X10 @ X11)
% 0.37/0.54           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.54            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.37/0.54          | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.54  thf(t4_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.54  thf(t98_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ X14 @ X15)
% 0.37/0.54           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf(t1_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('16', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.54  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.37/0.54          | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('demod', [status(thm)], ['12', '17'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (((sk_B_1)
% 0.37/0.54         != (k2_yellow19 @ sk_A @ 
% 0.37/0.54             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d2_yellow_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (k1_zfmisc_1 @ 
% 0.37/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf(t14_yellow19, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.54             ( m1_subset_1 @
% 0.37/0.54               B @ 
% 0.37/0.54               ( k1_zfmisc_1 @
% 0.37/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.54           ( ( k7_subset_1 @
% 0.37/0.54               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.37/0.54               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.37/0.54             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X26 : $i, X27 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ X26)
% 0.37/0.54          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.37/0.54          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.37/0.54          | ~ (m1_subset_1 @ X26 @ 
% 0.37/0.54               (k1_zfmisc_1 @ 
% 0.37/0.54                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))))
% 0.37/0.54          | ((k7_subset_1 @ 
% 0.37/0.54              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27))) @ X26 @ 
% 0.37/0.54              (k1_tarski @ k1_xboole_0))
% 0.37/0.54              = (k2_yellow19 @ X27 @ 
% 0.37/0.54                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.37/0.54          | ~ (l1_struct_0 @ X27)
% 0.37/0.54          | (v2_struct_0 @ X27))),
% 0.37/0.54      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X26 : $i, X27 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ X26)
% 0.37/0.54          | ~ (v2_waybel_0 @ X26 @ 
% 0.37/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.37/0.54          | ~ (v13_waybel_0 @ X26 @ 
% 0.37/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.37/0.54          | ~ (m1_subset_1 @ X26 @ 
% 0.37/0.54               (k1_zfmisc_1 @ 
% 0.37/0.54                (u1_struct_0 @ 
% 0.37/0.54                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))))
% 0.37/0.54          | ((k7_subset_1 @ 
% 0.37/0.54              (u1_struct_0 @ 
% 0.37/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27)))) @ 
% 0.37/0.54              X26 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.54              = (k2_yellow19 @ X27 @ 
% 0.37/0.54                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.37/0.54          | ~ (l1_struct_0 @ X27)
% 0.37/0.54          | (v2_struct_0 @ X27))),
% 0.37/0.54      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.54        | ((k7_subset_1 @ 
% 0.37/0.54            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.54            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.54            = (k2_yellow19 @ sk_A @ 
% 0.37/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.37/0.54        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.54        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['22', '28'])).
% 0.37/0.54  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (k1_zfmisc_1 @ 
% 0.37/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.37/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.37/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k7_subset_1 @ 
% 0.37/0.54           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.54           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      ((v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      ((v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.54            = (k2_yellow19 @ sk_A @ 
% 0.37/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.37/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('demod', [status(thm)], ['29', '30', '33', '36', '39'])).
% 0.37/0.54  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (((v1_xboole_0 @ sk_B_1)
% 0.37/0.54        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.54            = (k2_yellow19 @ sk_A @ 
% 0.37/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.54      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.54         = (k2_yellow19 @ sk_A @ 
% 0.37/0.54            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.54      inference('clc', [status(thm)], ['42', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['19', '44'])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['18', '45'])).
% 0.37/0.54  thf('47', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.37/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.37/0.54          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf(d3_struct_0, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (![X23 : $i]:
% 0.37/0.54         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (k1_zfmisc_1 @ 
% 0.37/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      (((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54         (k1_zfmisc_1 @ 
% 0.37/0.54          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.37/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.37/0.54  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('56', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (k1_zfmisc_1 @ 
% 0.37/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.54  thf(t2_yellow19, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.54             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.37/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.37/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.37/0.54             ( m1_subset_1 @
% 0.37/0.54               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.37/0.54           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ X28)
% 0.37/0.54          | ~ (v1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X29)))
% 0.37/0.54          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.37/0.54          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.37/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X29))))
% 0.37/0.54          | ~ (r2_hidden @ X30 @ X28)
% 0.37/0.54          | ~ (v1_xboole_0 @ X30)
% 0.37/0.54          | (v1_xboole_0 @ X29))),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('61', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('62', plain,
% 0.37/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ X28)
% 0.37/0.54          | ~ (v1_subset_1 @ X28 @ 
% 0.37/0.54               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29))))
% 0.37/0.54          | ~ (v2_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.37/0.54          | ~ (v13_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.37/0.54          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.54               (k1_zfmisc_1 @ 
% 0.37/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))))
% 0.37/0.54          | ~ (r2_hidden @ X30 @ X28)
% 0.37/0.54          | ~ (v1_xboole_0 @ X30)
% 0.37/0.54          | (v1_xboole_0 @ X29))),
% 0.37/0.54      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.37/0.54  thf('63', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.54          | ~ (v1_xboole_0 @ X0)
% 0.37/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.54          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.54          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.54          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.37/0.54               (u1_struct_0 @ 
% 0.37/0.54                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['56', '62'])).
% 0.37/0.54  thf('64', plain,
% 0.37/0.54      (![X23 : $i]:
% 0.37/0.54         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.54  thf('65', plain,
% 0.37/0.54      ((v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.54  thf('66', plain,
% 0.37/0.54      (((v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['64', '65'])).
% 0.37/0.54  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('68', plain,
% 0.37/0.54      ((v13_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.54  thf('69', plain,
% 0.37/0.54      (![X23 : $i]:
% 0.37/0.54         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.54  thf('70', plain,
% 0.37/0.54      ((v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.54  thf('71', plain,
% 0.37/0.54      (((v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['69', '70'])).
% 0.37/0.54  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('73', plain,
% 0.37/0.54      ((v2_waybel_0 @ sk_B_1 @ 
% 0.37/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['71', '72'])).
% 0.37/0.54  thf('74', plain,
% 0.37/0.54      (![X23 : $i]:
% 0.37/0.54         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.54  thf('75', plain,
% 0.37/0.54      ((v1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('76', plain,
% 0.37/0.54      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.54  thf('77', plain,
% 0.37/0.54      ((v1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.54  thf('78', plain,
% 0.37/0.54      (((v1_subset_1 @ sk_B_1 @ 
% 0.37/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['74', '77'])).
% 0.37/0.54  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('80', plain,
% 0.37/0.54      ((v1_subset_1 @ sk_B_1 @ 
% 0.37/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.54      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.54  thf('81', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.54          | ~ (v1_xboole_0 @ X0)
% 0.37/0.54          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('demod', [status(thm)], ['63', '68', '73', '80'])).
% 0.37/0.54  thf('82', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.37/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['51', '81'])).
% 0.37/0.54  thf('83', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0)
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['50', '82'])).
% 0.37/0.54  thf('84', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.37/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['83'])).
% 0.37/0.54  thf(fc2_struct_0, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.54  thf('85', plain,
% 0.37/0.54      (![X24 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.37/0.54          | ~ (l1_struct_0 @ X24)
% 0.37/0.54          | (v2_struct_0 @ X24))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.54  thf('86', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0)
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | (v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.54  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('88', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0)
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.54  thf('89', plain,
% 0.37/0.54      (![X16 : $i, X17 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ (k1_tarski @ X16) @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.37/0.54      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.37/0.54  thf('90', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54          | ~ (v1_xboole_0 @ X0)
% 0.37/0.54          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.54  thf('91', plain,
% 0.37/0.54      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.54        | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['47', '90'])).
% 0.37/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.54  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('93', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.54  thf('94', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('95', plain, ((v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('clc', [status(thm)], ['93', '94'])).
% 0.37/0.54  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
