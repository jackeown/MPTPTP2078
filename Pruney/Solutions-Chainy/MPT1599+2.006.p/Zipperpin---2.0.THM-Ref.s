%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lynuRT4R2h

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:06 EST 2020

% Result     : Theorem 21.93s
% Output     : Refutation 21.93s
% Verified   : 
% Statistics : Number of formulae       :  247 (1161 expanded)
%              Number of leaves         :   31 ( 377 expanded)
%              Depth                    :   23
%              Number of atoms          : 2988 (17566 expanded)
%              Number of equality atoms :   96 ( 252 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t7_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
                 => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_yellow_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r3_orders_2 @ X3 @ X4 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('11',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( B
                  = ( k12_lattice3 @ A @ B @ C ) )
              <=> ( r3_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_orders_2 @ X21 @ X20 @ X22 )
      | ( X20
        = ( k12_lattice3 @ X21 @ X20 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( sk_C
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('19',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('20',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( sk_C
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    | ( sk_C
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( sk_C
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k12_lattice3 @ X11 @ X10 @ X12 )
        = ( k11_lattice3 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('32',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k12_lattice3 @ X11 @ X10 @ X12 )
        = ( k11_lattice3 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('40',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','43','44'])).

thf('46',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['25','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('48',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('49',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k11_lattice3 @ A @ B @ C )
                = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( ( k11_lattice3 @ X14 @ X13 @ X15 )
        = ( k11_lattice3 @ X14 @ X15 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t15_lattice3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('54',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k12_lattice3 @ X11 @ X10 @ X12 )
        = ( k11_lattice3 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('63',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup+',[status(thm)],['46','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( X20
       != ( k12_lattice3 @ X21 @ X20 @ X22 ) )
      | ( r3_orders_2 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('73',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('74',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( v4_orders_2 @ A )
                   => ( ( k11_lattice3 @ A @ ( k11_lattice3 @ A @ B @ C ) @ D )
                      = ( k11_lattice3 @ A @ B @ ( k11_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( ( k11_lattice3 @ X17 @ ( k11_lattice3 @ X17 @ X16 @ X19 ) @ X18 )
        = ( k11_lattice3 @ X17 @ X16 @ ( k11_lattice3 @ X17 @ X19 @ X18 ) ) )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_lattice3])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ X1 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('86',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('88',plain,(
    ! [X28: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ X1 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf('94',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('97',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('107',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('109',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['98','109'])).

thf('111',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['79','110'])).

thf('112',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','111'])).

thf('113',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('115',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X31 ) @ X30 @ X32 )
      | ( r1_tarski @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ X1 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('128',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('132',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('133',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('135',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('138',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('141',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('144',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('147',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r3_orders_2 @ X3 @ X4 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('151',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_orders_2 @ X21 @ X20 @ X22 )
      | ( X20
        = ( k12_lattice3 @ X21 @ X20 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( sk_B
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('159',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('160',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( sk_B
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    | ( sk_B
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','162'])).

thf('164',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( sk_B
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','163'])).

thf('165',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('166',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
      = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( ( k11_lattice3 @ X14 @ X13 @ X15 )
        = ( k11_lattice3 @ X14 @ X15 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t15_lattice3])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('172',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['167','174'])).

thf('176',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('177',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','177'])).

thf('179',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','43','44'])).

thf('182',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('185',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('187',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['182','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('190',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['179','192'])).

thf('194',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('196',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','202'])).

thf('204',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('207',plain,(
    ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('210',plain,(
    ! [X6: $i] :
      ( ~ ( v2_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['208','211'])).

thf('213',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    $false ),
    inference(demod,[status(thm)],['212','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lynuRT4R2h
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 21.93/22.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.93/22.15  % Solved by: fo/fo7.sh
% 21.93/22.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.93/22.15  % done 4696 iterations in 21.698s
% 21.93/22.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.93/22.15  % SZS output start Refutation
% 21.93/22.15  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 21.93/22.15  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 21.93/22.15  thf(sk_C_type, type, sk_C: $i).
% 21.93/22.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.93/22.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 21.93/22.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 21.93/22.15  thf(sk_A_type, type, sk_A: $i).
% 21.93/22.15  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 21.93/22.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.93/22.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.93/22.15  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 21.93/22.15  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 21.93/22.15  thf(sk_B_type, type, sk_B: $i).
% 21.93/22.15  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 21.93/22.15  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 21.93/22.15  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 21.93/22.15  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 21.93/22.15  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 21.93/22.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 21.93/22.15  thf(t7_yellow_1, conjecture,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( ~( v1_xboole_0 @ A ) ) =>
% 21.93/22.15       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 21.93/22.15         ( ![B:$i]:
% 21.93/22.15           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15             ( ![C:$i]:
% 21.93/22.15               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15                 ( r1_tarski @
% 21.93/22.15                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 21.93/22.15                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 21.93/22.15  thf(zf_stmt_0, negated_conjecture,
% 21.93/22.15    (~( ![A:$i]:
% 21.93/22.15        ( ( ~( v1_xboole_0 @ A ) ) =>
% 21.93/22.15          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 21.93/22.15            ( ![B:$i]:
% 21.93/22.15              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15                ( ![C:$i]:
% 21.93/22.15                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15                    ( r1_tarski @
% 21.93/22.15                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 21.93/22.15                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 21.93/22.15    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 21.93/22.15  thf('0', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('1', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf(dt_k11_lattice3, axiom,
% 21.93/22.15    (![A:$i,B:$i,C:$i]:
% 21.93/22.15     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 21.93/22.15         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 21.93/22.15       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 21.93/22.15  thf('2', plain,
% 21.93/22.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 21.93/22.15          | ~ (l1_orders_2 @ X8)
% 21.93/22.15          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 21.93/22.15          | (m1_subset_1 @ (k11_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 21.93/22.15  thf('3', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 21.93/22.15           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['1', '2'])).
% 21.93/22.15  thf(dt_k2_yellow_1, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 21.93/22.15       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 21.93/22.15  thf('4', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('5', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 21.93/22.15           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['3', '4'])).
% 21.93/22.15  thf('6', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['0', '5'])).
% 21.93/22.15  thf('7', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf(reflexivity_r3_orders_2, axiom,
% 21.93/22.15    (![A:$i,B:$i,C:$i]:
% 21.93/22.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 21.93/22.15         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 21.93/22.15         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 21.93/22.15       ( r3_orders_2 @ A @ B @ B ) ))).
% 21.93/22.15  thf('8', plain,
% 21.93/22.15      (![X3 : $i, X4 : $i, X5 : $i]:
% 21.93/22.15         ((r3_orders_2 @ X3 @ X4 @ X4)
% 21.93/22.15          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 21.93/22.15          | ~ (l1_orders_2 @ X3)
% 21.93/22.15          | ~ (v3_orders_2 @ X3)
% 21.93/22.15          | (v2_struct_0 @ X3)
% 21.93/22.15          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3)))),
% 21.93/22.15      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 21.93/22.15  thf('9', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['7', '8'])).
% 21.93/22.15  thf(fc5_yellow_1, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 21.93/22.15       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 21.93/22.15       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 21.93/22.15       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 21.93/22.15  thf('10', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('11', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('12', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['9', '10', '11'])).
% 21.93/22.15  thf('13', plain,
% 21.93/22.15      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['6', '12'])).
% 21.93/22.15  thf('14', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('15', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf(t25_yellow_0, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 21.93/22.15         ( l1_orders_2 @ A ) ) =>
% 21.93/22.15       ( ![B:$i]:
% 21.93/22.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15           ( ![C:$i]:
% 21.93/22.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15               ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 21.93/22.15                 ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 21.93/22.15  thf('16', plain,
% 21.93/22.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ~ (r3_orders_2 @ X21 @ X20 @ X22)
% 21.93/22.15          | ((X20) = (k12_lattice3 @ X21 @ X20 @ X22))
% 21.93/22.15          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ~ (l1_orders_2 @ X21)
% 21.93/22.15          | ~ (v2_lattice3 @ X21)
% 21.93/22.15          | ~ (v5_orders_2 @ X21)
% 21.93/22.15          | ~ (v3_orders_2 @ X21))),
% 21.93/22.15      inference('cnf', [status(esa)], [t25_yellow_0])).
% 21.93/22.15  thf('17', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))),
% 21.93/22.15      inference('sup-', [status(thm)], ['15', '16'])).
% 21.93/22.15  thf('18', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('19', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('20', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('21', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('22', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))),
% 21.93/22.15      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 21.93/22.15  thf('23', plain,
% 21.93/22.15      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 21.93/22.15        | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['14', '22'])).
% 21.93/22.15  thf('24', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['13', '23'])).
% 21.93/22.15  thf('25', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('26', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('27', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 21.93/22.15           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['3', '4'])).
% 21.93/22.15  thf('28', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['26', '27'])).
% 21.93/22.15  thf(redefinition_k12_lattice3, axiom,
% 21.93/22.15    (![A:$i,B:$i,C:$i]:
% 21.93/22.15     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 21.93/22.15         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 21.93/22.15         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 21.93/22.15       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 21.93/22.15  thf('29', plain,
% 21.93/22.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ~ (l1_orders_2 @ X11)
% 21.93/22.15          | ~ (v2_lattice3 @ X11)
% 21.93/22.15          | ~ (v5_orders_2 @ X11)
% 21.93/22.15          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ((k12_lattice3 @ X11 @ X10 @ X12)
% 21.93/22.15              = (k11_lattice3 @ X11 @ X10 @ X12)))),
% 21.93/22.15      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 21.93/22.15  thf('30', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['28', '29'])).
% 21.93/22.15  thf('31', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('32', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('33', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('34', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 21.93/22.15  thf('35', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('36', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('37', plain,
% 21.93/22.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ~ (l1_orders_2 @ X11)
% 21.93/22.15          | ~ (v2_lattice3 @ X11)
% 21.93/22.15          | ~ (v5_orders_2 @ X11)
% 21.93/22.15          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ((k12_lattice3 @ X11 @ X10 @ X12)
% 21.93/22.15              = (k11_lattice3 @ X11 @ X10 @ X12)))),
% 21.93/22.15      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 21.93/22.15  thf('38', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['36', '37'])).
% 21.93/22.15  thf('39', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('40', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('41', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('42', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 21.93/22.15  thf('43', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('44', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('45', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['34', '43', '44'])).
% 21.93/22.15  thf('46', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['25', '45'])).
% 21.93/22.15  thf('47', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['26', '27'])).
% 21.93/22.15  thf('48', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('49', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf('50', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf(t15_lattice3, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 21.93/22.15       ( ![B:$i]:
% 21.93/22.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15           ( ![C:$i]:
% 21.93/22.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15               ( ( k11_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 21.93/22.15  thf('51', plain,
% 21.93/22.15      (![X13 : $i, X14 : $i, X15 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 21.93/22.15          | ((k11_lattice3 @ X14 @ X13 @ X15)
% 21.93/22.15              = (k11_lattice3 @ X14 @ X15 @ X13))
% 21.93/22.15          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 21.93/22.15          | ~ (l1_orders_2 @ X14)
% 21.93/22.15          | ~ (v2_lattice3 @ X14)
% 21.93/22.15          | ~ (v5_orders_2 @ X14))),
% 21.93/22.15      inference('cnf', [status(esa)], [t15_lattice3])).
% 21.93/22.15  thf('52', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['50', '51'])).
% 21.93/22.15  thf('53', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('54', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('55', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('56', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 21.93/22.15      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 21.93/22.15  thf('57', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['49', '56'])).
% 21.93/22.15  thf('58', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf('59', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('60', plain,
% 21.93/22.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ~ (l1_orders_2 @ X11)
% 21.93/22.15          | ~ (v2_lattice3 @ X11)
% 21.93/22.15          | ~ (v5_orders_2 @ X11)
% 21.93/22.15          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 21.93/22.15          | ((k12_lattice3 @ X11 @ X10 @ X12)
% 21.93/22.15              = (k11_lattice3 @ X11 @ X10 @ X12)))),
% 21.93/22.15      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 21.93/22.15  thf('61', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['59', '60'])).
% 21.93/22.15  thf('62', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('63', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('64', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('65', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 21.93/22.15  thf('66', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['58', '65'])).
% 21.93/22.15  thf('67', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['57', '66'])).
% 21.93/22.15  thf('68', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('sup+', [status(thm)], ['46', '67'])).
% 21.93/22.15  thf('69', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf('70', plain,
% 21.93/22.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ((X20) != (k12_lattice3 @ X21 @ X20 @ X22))
% 21.93/22.15          | (r3_orders_2 @ X21 @ X20 @ X22)
% 21.93/22.15          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ~ (l1_orders_2 @ X21)
% 21.93/22.15          | ~ (v2_lattice3 @ X21)
% 21.93/22.15          | ~ (v5_orders_2 @ X21)
% 21.93/22.15          | ~ (v3_orders_2 @ X21))),
% 21.93/22.15      inference('cnf', [status(esa)], [t25_yellow_0])).
% 21.93/22.15  thf('71', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15              != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15                  (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['69', '70'])).
% 21.93/22.15  thf('72', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('73', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('74', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('75', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('76', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15              != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15                  (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)))),
% 21.93/22.15      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 21.93/22.15  thf('77', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 21.93/22.15        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('sup-', [status(thm)], ['68', '76'])).
% 21.93/22.15  thf('78', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('79', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['77', '78'])).
% 21.93/22.15  thf('80', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('81', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('82', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf(t16_lattice3, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 21.93/22.15       ( ![B:$i]:
% 21.93/22.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15           ( ![C:$i]:
% 21.93/22.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15               ( ![D:$i]:
% 21.93/22.15                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 21.93/22.15                   ( ( v4_orders_2 @ A ) =>
% 21.93/22.15                     ( ( k11_lattice3 @ A @ ( k11_lattice3 @ A @ B @ C ) @ D ) =
% 21.93/22.15                       ( k11_lattice3 @ A @ B @ ( k11_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 21.93/22.15  thf('83', plain,
% 21.93/22.15      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 21.93/22.15          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 21.93/22.15          | ((k11_lattice3 @ X17 @ (k11_lattice3 @ X17 @ X16 @ X19) @ X18)
% 21.93/22.15              = (k11_lattice3 @ X17 @ X16 @ (k11_lattice3 @ X17 @ X19 @ X18)))
% 21.93/22.15          | ~ (v4_orders_2 @ X17)
% 21.93/22.15          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 21.93/22.15          | ~ (l1_orders_2 @ X17)
% 21.93/22.15          | ~ (v2_lattice3 @ X17)
% 21.93/22.15          | ~ (v5_orders_2 @ X17))),
% 21.93/22.15      inference('cnf', [status(esa)], [t16_lattice3])).
% 21.93/22.15  thf('84', plain,
% 21.93/22.15      (![X0 : $i, X1 : $i]:
% 21.93/22.15         (~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (v4_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ X1)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)))
% 21.93/22.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('sup-', [status(thm)], ['82', '83'])).
% 21.93/22.15  thf('85', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('86', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('87', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('88', plain, (![X28 : $i]: (v4_orders_2 @ (k2_yellow_1 @ X28))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('89', plain,
% 21.93/22.15      (![X0 : $i, X1 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ X1)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)))
% 21.93/22.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 21.93/22.15  thf('90', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))))),
% 21.93/22.15      inference('sup-', [status(thm)], ['81', '89'])).
% 21.93/22.15  thf('91', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('92', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))))),
% 21.93/22.15      inference('demod', [status(thm)], ['90', '91'])).
% 21.93/22.15  thf('93', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['80', '92'])).
% 21.93/22.15  thf('94', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['57', '66'])).
% 21.93/22.15  thf('95', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('96', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 21.93/22.15  thf('97', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['95', '96'])).
% 21.93/22.15  thf('98', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 21.93/22.15      inference('demod', [status(thm)], ['93', '94', '97'])).
% 21.93/22.15  thf('99', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('100', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('101', plain,
% 21.93/22.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 21.93/22.15          | ~ (l1_orders_2 @ X8)
% 21.93/22.15          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 21.93/22.15          | (m1_subset_1 @ (k11_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 21.93/22.15  thf('102', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ 
% 21.93/22.15           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['100', '101'])).
% 21.93/22.15  thf('103', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('104', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ 
% 21.93/22.15           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['102', '103'])).
% 21.93/22.15  thf('105', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['99', '104'])).
% 21.93/22.15  thf('106', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['95', '96'])).
% 21.93/22.15  thf('107', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['105', '106'])).
% 21.93/22.15  thf('108', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 21.93/22.15  thf('109', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['107', '108'])).
% 21.93/22.15  thf('110', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))
% 21.93/22.15         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('sup+', [status(thm)], ['98', '109'])).
% 21.93/22.15  thf('111', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['79', '110'])).
% 21.93/22.15  thf('112', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['24', '111'])).
% 21.93/22.15  thf('113', plain,
% 21.93/22.15      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('simplify', [status(thm)], ['112'])).
% 21.93/22.15  thf('114', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf(t3_yellow_1, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( ~( v1_xboole_0 @ A ) ) =>
% 21.93/22.15       ( ![B:$i]:
% 21.93/22.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15           ( ![C:$i]:
% 21.93/22.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 21.93/22.15               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 21.93/22.15                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 21.93/22.15  thf('115', plain,
% 21.93/22.15      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ X31) @ X30 @ X32)
% 21.93/22.15          | (r1_tarski @ X30 @ X32)
% 21.93/22.15          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 21.93/22.15          | (v1_xboole_0 @ X31))),
% 21.93/22.15      inference('cnf', [status(esa)], [t3_yellow_1])).
% 21.93/22.15  thf('116', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((v1_xboole_0 @ sk_A)
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15             X0)
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 21.93/22.15      inference('sup-', [status(thm)], ['114', '115'])).
% 21.93/22.15  thf('117', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15           sk_C)
% 21.93/22.15        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15        | (v1_xboole_0 @ sk_A))),
% 21.93/22.15      inference('sup-', [status(thm)], ['113', '116'])).
% 21.93/22.15  thf('118', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('119', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15           sk_C)
% 21.93/22.15        | (v1_xboole_0 @ sk_A))),
% 21.93/22.15      inference('demod', [status(thm)], ['117', '118'])).
% 21.93/22.15  thf('120', plain, (~ (v1_xboole_0 @ sk_A)),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('121', plain,
% 21.93/22.15      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('clc', [status(thm)], ['119', '120'])).
% 21.93/22.15  thf('122', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('123', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('124', plain,
% 21.93/22.15      (![X0 : $i, X1 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ X1)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)))
% 21.93/22.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 21.93/22.15  thf('125', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))))),
% 21.93/22.15      inference('sup-', [status(thm)], ['123', '124'])).
% 21.93/22.15  thf('126', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('127', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 21.93/22.15  thf('128', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['126', '127'])).
% 21.93/22.15  thf('129', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))))),
% 21.93/22.15      inference('demod', [status(thm)], ['125', '128'])).
% 21.93/22.15  thf('130', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['122', '129'])).
% 21.93/22.15  thf('131', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['0', '5'])).
% 21.93/22.15  thf('132', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['126', '127'])).
% 21.93/22.15  thf('133', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['131', '132'])).
% 21.93/22.15  thf('134', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 21.93/22.15      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 21.93/22.15  thf('135', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['133', '134'])).
% 21.93/22.15  thf('136', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['131', '132'])).
% 21.93/22.15  thf('137', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 21.93/22.15  thf('138', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['136', '137'])).
% 21.93/22.15  thf('139', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['135', '138'])).
% 21.93/22.15  thf('140', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('141', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('demod', [status(thm)], ['130', '139', '140'])).
% 21.93/22.15  thf('142', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf('143', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 21.93/22.15  thf('144', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['142', '143'])).
% 21.93/22.15  thf('145', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 21.93/22.15      inference('sup+', [status(thm)], ['141', '144'])).
% 21.93/22.15  thf('146', plain,
% 21.93/22.15      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['0', '5'])).
% 21.93/22.15  thf('147', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('148', plain,
% 21.93/22.15      (![X3 : $i, X4 : $i, X5 : $i]:
% 21.93/22.15         ((r3_orders_2 @ X3 @ X4 @ X4)
% 21.93/22.15          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 21.93/22.15          | ~ (l1_orders_2 @ X3)
% 21.93/22.15          | ~ (v3_orders_2 @ X3)
% 21.93/22.15          | (v2_struct_0 @ X3)
% 21.93/22.15          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3)))),
% 21.93/22.15      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 21.93/22.15  thf('149', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['147', '148'])).
% 21.93/22.15  thf('150', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('151', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('152', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 21.93/22.15      inference('demod', [status(thm)], ['149', '150', '151'])).
% 21.93/22.15  thf('153', plain,
% 21.93/22.15      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['146', '152'])).
% 21.93/22.15  thf('154', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('155', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('156', plain,
% 21.93/22.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ~ (r3_orders_2 @ X21 @ X20 @ X22)
% 21.93/22.15          | ((X20) = (k12_lattice3 @ X21 @ X20 @ X22))
% 21.93/22.15          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 21.93/22.15          | ~ (l1_orders_2 @ X21)
% 21.93/22.15          | ~ (v2_lattice3 @ X21)
% 21.93/22.15          | ~ (v5_orders_2 @ X21)
% 21.93/22.15          | ~ (v3_orders_2 @ X21))),
% 21.93/22.15      inference('cnf', [status(esa)], [t25_yellow_0])).
% 21.93/22.15  thf('157', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))),
% 21.93/22.15      inference('sup-', [status(thm)], ['155', '156'])).
% 21.93/22.15  thf('158', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('159', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('160', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('161', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('162', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))),
% 21.93/22.15      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 21.93/22.15  thf('163', plain,
% 21.93/22.15      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 21.93/22.15        | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['154', '162'])).
% 21.93/22.15  thf('164', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['153', '163'])).
% 21.93/22.15  thf('165', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['136', '137'])).
% 21.93/22.15  thf('166', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15          (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15          = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup+', [status(thm)], ['164', '165'])).
% 21.93/22.15  thf('167', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('168', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('169', plain,
% 21.93/22.15      (![X13 : $i, X14 : $i, X15 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 21.93/22.15          | ((k11_lattice3 @ X14 @ X13 @ X15)
% 21.93/22.15              = (k11_lattice3 @ X14 @ X15 @ X13))
% 21.93/22.15          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 21.93/22.15          | ~ (l1_orders_2 @ X14)
% 21.93/22.15          | ~ (v2_lattice3 @ X14)
% 21.93/22.15          | ~ (v5_orders_2 @ X14))),
% 21.93/22.15      inference('cnf', [status(esa)], [t15_lattice3])).
% 21.93/22.15  thf('170', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['168', '169'])).
% 21.93/22.15  thf('171', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 21.93/22.15      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 21.93/22.15  thf('172', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('173', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf('174', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 21.93/22.15      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 21.93/22.15  thf('175', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['167', '174'])).
% 21.93/22.15  thf('176', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('177', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 21.93/22.15      inference('demod', [status(thm)], ['175', '176'])).
% 21.93/22.15  thf('178', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 21.93/22.15          (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 21.93/22.15          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['166', '177'])).
% 21.93/22.15  thf('179', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15          (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup+', [status(thm)], ['145', '178'])).
% 21.93/22.15  thf('180', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('181', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('demod', [status(thm)], ['34', '43', '44'])).
% 21.93/22.15  thf('182', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['180', '181'])).
% 21.93/22.15  thf('183', plain,
% 21.93/22.15      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('demod', [status(thm)], ['47', '48'])).
% 21.93/22.15  thf('184', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 21.93/22.15              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 21.93/22.15      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 21.93/22.15  thf('185', plain,
% 21.93/22.15      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['183', '184'])).
% 21.93/22.15  thf('186', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['142', '143'])).
% 21.93/22.15  thf('187', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('demod', [status(thm)], ['185', '186'])).
% 21.93/22.15  thf('188', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('sup+', [status(thm)], ['182', '187'])).
% 21.93/22.15  thf('189', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 21.93/22.15          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15              != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15                  (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)))),
% 21.93/22.15      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 21.93/22.15  thf('190', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 21.93/22.15        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 21.93/22.15      inference('sup-', [status(thm)], ['188', '189'])).
% 21.93/22.15  thf('191', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('192', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 21.93/22.15              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('demod', [status(thm)], ['190', '191'])).
% 21.93/22.15  thf('193', plain,
% 21.93/22.15      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 21.93/22.15      inference('sup-', [status(thm)], ['179', '192'])).
% 21.93/22.15  thf('194', plain,
% 21.93/22.15      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('simplify', [status(thm)], ['193'])).
% 21.93/22.15  thf('195', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((v1_xboole_0 @ sk_A)
% 21.93/22.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15          | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15             X0)
% 21.93/22.15          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 21.93/22.15               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 21.93/22.15      inference('sup-', [status(thm)], ['114', '115'])).
% 21.93/22.15  thf('196', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15           sk_B)
% 21.93/22.15        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 21.93/22.15        | (v1_xboole_0 @ sk_A))),
% 21.93/22.15      inference('sup-', [status(thm)], ['194', '195'])).
% 21.93/22.15  thf('197', plain,
% 21.93/22.15      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('198', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15           sk_B)
% 21.93/22.15        | (v1_xboole_0 @ sk_A))),
% 21.93/22.15      inference('demod', [status(thm)], ['196', '197'])).
% 21.93/22.15  thf('199', plain, (~ (v1_xboole_0 @ sk_A)),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('200', plain,
% 21.93/22.15      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('clc', [status(thm)], ['198', '199'])).
% 21.93/22.15  thf(t19_xboole_1, axiom,
% 21.93/22.15    (![A:$i,B:$i,C:$i]:
% 21.93/22.15     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 21.93/22.15       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 21.93/22.15  thf('201', plain,
% 21.93/22.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.93/22.15         (~ (r1_tarski @ X0 @ X1)
% 21.93/22.15          | ~ (r1_tarski @ X0 @ X2)
% 21.93/22.15          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 21.93/22.15      inference('cnf', [status(esa)], [t19_xboole_1])).
% 21.93/22.15  thf('202', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15          | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15             (k3_xboole_0 @ sk_B @ X0))
% 21.93/22.15          | ~ (r1_tarski @ 
% 21.93/22.15               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 21.93/22.15      inference('sup-', [status(thm)], ['200', '201'])).
% 21.93/22.15  thf('203', plain,
% 21.93/22.15      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 21.93/22.15        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15           (k3_xboole_0 @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['121', '202'])).
% 21.93/22.15  thf('204', plain,
% 21.93/22.15      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15         (k3_xboole_0 @ sk_B @ sk_C))
% 21.93/22.15        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 21.93/22.15      inference('simplify', [status(thm)], ['203'])).
% 21.93/22.15  thf('205', plain,
% 21.93/22.15      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15          (k3_xboole_0 @ sk_B @ sk_C))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('206', plain,
% 21.93/22.15      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 21.93/22.15         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 21.93/22.15      inference('sup-', [status(thm)], ['35', '42'])).
% 21.93/22.15  thf('207', plain,
% 21.93/22.15      (~ (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 21.93/22.15          (k3_xboole_0 @ sk_B @ sk_C))),
% 21.93/22.15      inference('demod', [status(thm)], ['205', '206'])).
% 21.93/22.15  thf('208', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('clc', [status(thm)], ['204', '207'])).
% 21.93/22.15  thf('209', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 21.93/22.15      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 21.93/22.15  thf(cc2_lattice3, axiom,
% 21.93/22.15    (![A:$i]:
% 21.93/22.15     ( ( l1_orders_2 @ A ) =>
% 21.93/22.15       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 21.93/22.15  thf('210', plain,
% 21.93/22.15      (![X6 : $i]:
% 21.93/22.15         (~ (v2_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 21.93/22.15      inference('cnf', [status(esa)], [cc2_lattice3])).
% 21.93/22.15  thf('211', plain,
% 21.93/22.15      (![X0 : $i]:
% 21.93/22.15         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 21.93/22.15          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 21.93/22.15      inference('sup-', [status(thm)], ['209', '210'])).
% 21.93/22.15  thf('212', plain, (~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('sup-', [status(thm)], ['208', '211'])).
% 21.93/22.15  thf('213', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 21.93/22.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.93/22.15  thf('214', plain, ($false), inference('demod', [status(thm)], ['212', '213'])).
% 21.93/22.15  
% 21.93/22.15  % SZS output end Refutation
% 21.93/22.15  
% 21.93/22.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
