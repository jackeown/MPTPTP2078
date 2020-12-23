%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IPHiPxfjjU

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:49 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 208 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   22
%              Number of atoms          :  769 (2155 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t53_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_yellow_0 @ A @ B ) )
       => ( v3_lattice3 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_yellow_0 @ A @ B ) )
         => ( v3_lattice3 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_yellow_0])).

thf('6',plain,(
    ! [X22: $i] :
      ( ( r1_yellow_0 @ sk_A @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t50_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
           => ( r2_yellow_0 @ A @ B ) )
          & ( ( r2_yellow_0 @ A @ B )
           => ( r2_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) )
          & ( ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) )
           => ( r1_yellow_0 @ A @ B ) )
          & ( ( r1_yellow_0 @ A @ B )
           => ( r1_yellow_0 @ A @ ( k3_xboole_0 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X20: $i] :
      ( ~ ( r1_yellow_0 @ X17 @ ( k3_xboole_0 @ X20 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_yellow_0 @ X17 @ X20 )
      | ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t50_yellow_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8
       != ( k1_yellow_0 @ X6 @ X7 ) )
      | ( r2_lattice3 @ X6 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_yellow_0 @ X6 @ X7 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( r1_yellow_0 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r2_lattice3 @ X6 @ X7 @ ( k1_yellow_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d12_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                 => ( r1_orders_2 @ A @ C @ D ) ) )
            & ( r2_lattice3 @ A @ B @ C )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X3 @ ( sk_B @ X3 ) @ ( sk_D @ X2 @ X3 ) )
      | ~ ( r2_lattice3 @ X3 @ ( sk_B @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( v3_lattice3 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v3_lattice3 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( sk_D @ ( k1_yellow_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( sk_D @ ( k1_yellow_0 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v3_lattice3 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v3_lattice3 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v3_lattice3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_lattice3 @ X3 @ ( sk_B @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( v3_lattice3 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('34',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v3_lattice3 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v3_lattice3 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v3_lattice3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k1_yellow_0 @ X6 @ X7 ) )
      | ~ ( r2_lattice3 @ X6 @ X7 @ X9 )
      | ( r1_orders_2 @ X6 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_yellow_0 @ X6 @ X7 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('44',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( r1_yellow_0 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( r1_orders_2 @ X6 @ ( k1_yellow_0 @ X6 @ X7 ) @ X9 )
      | ~ ( r2_lattice3 @ X6 @ X7 @ X9 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( sk_D @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X3 @ X2 @ ( sk_D @ X2 @ X3 ) )
      | ~ ( r2_lattice3 @ X3 @ ( sk_B @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( v3_lattice3 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('53',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v3_lattice3 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('56',plain,
    ( ( v3_lattice3 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v3_lattice3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).


%------------------------------------------------------------------------------
