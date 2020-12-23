%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x89s3qeWbL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 377 expanded)
%              Number of leaves         :   45 ( 147 expanded)
%              Depth                    :   17
%              Number of atoms          : 1249 (3642 expanded)
%              Number of equality atoms :   76 ( 332 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t17_yellow_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k2_xboole_0 @ B @ C ) )
            & ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k3_xboole_0 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
           => ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
                = ( k2_xboole_0 @ B @ C ) )
              & ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
                = ( k3_xboole_0 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( k3_yellow_1 @ X37 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(l19_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) )
            & ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X34 @ X32 ) @ ( k9_setfam_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ X34 @ X32 ) ) @ ( k9_setfam_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_B_1 ) ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X34 @ X32 ) @ ( k9_setfam_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ( r2_hidden @ ( k1_setfam_1 @ ( k2_tarski @ X34 @ X32 ) ) @ ( k9_setfam_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    r2_hidden @ ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf(t9_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ A )
               => ( ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C )
                  = ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X41 @ X43 ) @ X42 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X42 ) @ X41 @ X43 )
        = ( k3_xboole_0 @ X41 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_1])).

thf('27',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ~ ( r2_hidden @ ( k1_setfam_1 @ ( k2_tarski @ X41 @ X43 ) ) @ X42 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X42 ) @ X41 @ X43 )
        = ( k1_setfam_1 @ ( k2_tarski @ X41 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k11_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    ! [X37: $i] :
      ( ( k3_yellow_1 @ X37 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k12_lattice3 @ X13 @ X12 @ X14 )
        = ( k11_lattice3 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('42',plain,(
    ! [X37: $i] :
      ( ( k3_yellow_1 @ X37 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t12_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v3_lattice3 @ A )
       => ( ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X18: $i] :
      ( ~ ( v3_lattice3 @ X18 )
      | ( v2_lattice3 @ X18 )
      | ~ ( l1_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_lattice3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_lattice3 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc8_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v3_lattice3 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X31: $i] :
      ( v3_lattice3 @ ( k3_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','52'])).

thf('54',plain,
    ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','54','55'])).

thf('57',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('60',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) ) )
   <= ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ X34 @ X32 ) ) @ ( k9_setfam_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t8_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ A )
               => ( ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C )
                  = ( k2_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ ( k2_yellow_1 @ X39 ) ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X38 @ X40 ) @ X39 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X39 ) @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ ( k2_yellow_1 @ X39 ) ) )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t8_yellow_1])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('70',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('71',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ X38 @ X40 ) ) @ X39 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X39 ) @ X38 @ X40 )
        = ( k3_tarski @ ( k2_tarski @ X38 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k10_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 @ sk_C )
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('74',plain,(
    ! [X37: $i] :
      ( ( k3_yellow_1 @ X37 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k13_lattice3 @ X16 @ X15 @ X17 )
        = ( k10_lattice3 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('81',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('83',plain,(
    ! [X18: $i] :
      ( ~ ( v3_lattice3 @ X18 )
      | ( v1_lattice3 @ X18 )
      | ~ ( l1_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_lattice3])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_lattice3 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X31: $i] :
      ( v3_lattice3 @ ( k3_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X25: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','90'])).

thf('92',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('96',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['57'])).

thf('98',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('100',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) )
     != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['57'])).

thf('103',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['60','103'])).

thf('105',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['56','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['14','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x89s3qeWbL
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:57:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 118 iterations in 0.045s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.49  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.49  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.20/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.49  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(t17_yellow_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49               ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49             ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49               ( k3_xboole_0 @ B @ C ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49              ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                  ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49                ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                  ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t17_yellow_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_yellow_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X37 : $i]: ((k3_yellow_1 @ X37) = (k2_yellow_1 @ (k9_setfam_1 @ X37)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf(t1_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.49       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('2', plain, (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(l19_yellow_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) & 
% 0.20/0.49             ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k3_yellow_1 @ X33)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X34 @ X32) @ (k9_setfam_1 @ X33))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k3_yellow_1 @ X33))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(l51_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (k9_setfam_1 @ X33))
% 0.20/0.49          | (r2_hidden @ (k3_tarski @ (k2_tarski @ X34 @ X32)) @ 
% 0.20/0.49             (k9_setfam_1 @ X33))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (k9_setfam_1 @ X33)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k3_tarski @ (k2_tarski @ X0 @ sk_B_1)) @ 
% 0.20/0.49             (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((r2_hidden @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1)) @ 
% 0.20/0.49        (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('14', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('18', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k3_yellow_1 @ X33)))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X34 @ X32) @ (k9_setfam_1 @ X33))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k3_yellow_1 @ X33))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t12_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (k9_setfam_1 @ X33))
% 0.20/0.49          | (r2_hidden @ (k1_setfam_1 @ (k2_tarski @ X34 @ X32)) @ 
% 0.20/0.49             (k9_setfam_1 @ X33))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (k9_setfam_1 @ X33)))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.20/0.49             (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((r2_hidden @ (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ sk_C)) @ 
% 0.20/0.49        (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '24'])).
% 0.20/0.49  thf(t9_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.49                 ( ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X41 @ (u1_struct_0 @ (k2_yellow_1 @ X42)))
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X41 @ X43) @ X42)
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ X42) @ X41 @ X43)
% 0.20/0.49              = (k3_xboole_0 @ X41 @ X43))
% 0.20/0.49          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ (k2_yellow_1 @ X42)))
% 0.20/0.49          | (v1_xboole_0 @ X42))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_yellow_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X41 @ X42)
% 0.20/0.49          | ~ (r2_hidden @ (k1_setfam_1 @ (k2_tarski @ X41 @ X43)) @ X42)
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ X42) @ X41 @ X43)
% 0.20/0.49              = (k1_setfam_1 @ (k2_tarski @ X41 @ X43)))
% 0.20/0.49          | ~ (m1_subset_1 @ X43 @ X42)
% 0.20/0.49          | (v1_xboole_0 @ X42))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k11_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ sk_C)))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.49  thf('33', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X37 : $i]: ((k3_yellow_1 @ X37) = (k2_yellow_1 @ (k9_setfam_1 @ X37)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('35', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('36', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.49          | ~ (l1_orders_2 @ X13)
% 0.20/0.49          | ~ (v2_lattice3 @ X13)
% 0.20/0.49          | ~ (v5_orders_2 @ X13)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.49          | ((k12_lattice3 @ X13 @ X12 @ X14)
% 0.20/0.49              = (k11_lattice3 @ X13 @ X12 @ X14)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(fc7_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v4_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v3_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( ~( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) ))).
% 0.20/0.49  thf('41', plain, (![X29 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X37 : $i]: ((k3_yellow_1 @ X37) = (k2_yellow_1 @ (k9_setfam_1 @ X37)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf(dt_k2_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.49  thf('43', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.49  thf('44', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf(t12_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ( v3_lattice3 @ A ) => ( ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) ) ) ))).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         (~ (v3_lattice3 @ X18)
% 0.20/0.49          | (v2_lattice3 @ X18)
% 0.20/0.49          | ~ (l1_orders_2 @ X18)
% 0.20/0.49          | (v2_struct_0 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_lattice3])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v3_lattice3 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf(fc8_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v3_lattice3 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ))).
% 0.20/0.49  thf('47', plain, (![X31 : $i]: (v3_lattice3 @ (k3_yellow_1 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc8_yellow_1])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_lattice3 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, (![X25 : $i]: ~ (v2_struct_0 @ (k3_yellow_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf('50', plain, (![X0 : $i]: (v2_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41', '50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '53'])).
% 0.20/0.49  thf('55', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34', '54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            != (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k3_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k3_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ sk_C))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k3_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('62', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (k9_setfam_1 @ X33))
% 0.20/0.49          | (r2_hidden @ (k3_tarski @ (k2_tarski @ X34 @ X32)) @ 
% 0.20/0.49             (k9_setfam_1 @ X33))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (k9_setfam_1 @ X33)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k3_tarski @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.20/0.49             (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      ((r2_hidden @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)) @ 
% 0.20/0.49        (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '64'])).
% 0.20/0.49  thf(t8_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.49                 ( ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                   ( k2_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ (k2_yellow_1 @ X39)))
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X38 @ X40) @ X39)
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ X39) @ X38 @ X40)
% 0.20/0.49              = (k2_xboole_0 @ X38 @ X40))
% 0.20/0.49          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ (k2_yellow_1 @ X39)))
% 0.20/0.49          | (v1_xboole_0 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_yellow_1])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X38 @ X39)
% 0.20/0.49          | ~ (r2_hidden @ (k3_tarski @ (k2_tarski @ X38 @ X40)) @ X39)
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ X39) @ X38 @ X40)
% 0.20/0.49              = (k3_tarski @ (k2_tarski @ X38 @ X40)))
% 0.20/0.49          | ~ (m1_subset_1 @ X40 @ X39)
% 0.20/0.49          | (v1_xboole_0 @ X39))),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k10_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['65', '71'])).
% 0.20/0.49  thf('73', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (![X37 : $i]: ((k3_yellow_1 @ X37) = (k2_yellow_1 @ (k9_setfam_1 @ X37)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('75', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('76', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(redefinition_k13_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.49          | ~ (l1_orders_2 @ X16)
% 0.20/0.49          | ~ (v1_lattice3 @ X16)
% 0.20/0.49          | ~ (v5_orders_2 @ X16)
% 0.20/0.49          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.20/0.49          | ((k13_lattice3 @ X16 @ X15 @ X17)
% 0.20/0.49              = (k10_lattice3 @ X16 @ X15 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('81', plain, (![X29 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf('82', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         (~ (v3_lattice3 @ X18)
% 0.20/0.49          | (v1_lattice3 @ X18)
% 0.20/0.49          | ~ (l1_orders_2 @ X18)
% 0.20/0.49          | (v2_struct_0 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_lattice3])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v3_lattice3 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.49  thf('85', plain, (![X31 : $i]: (v3_lattice3 @ (k3_yellow_1 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc8_yellow_1])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v1_lattice3 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('87', plain, (![X25 : $i]: ~ (v2_struct_0 @ (k3_yellow_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf('88', plain, (![X0 : $i]: (v1_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.49  thf('89', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['76', '90'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['75', '91'])).
% 0.20/0.49  thf('93', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['72', '73', '74', '92', '93'])).
% 0.20/0.49  thf('95', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['57'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      ((((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.49          != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      ((((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C))
% 0.20/0.49          != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B_1 @ sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['57'])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 0.20/0.49  thf('104', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         != (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['60', '103'])).
% 0.20/0.49  thf('105', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['56', '104'])).
% 0.20/0.49  thf('106', plain, ($false), inference('demod', [status(thm)], ['14', '105'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
