%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q1K5ZcA98D

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 189 expanded)
%              Number of leaves         :   45 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  968 (2303 expanded)
%              Number of equality atoms :   59 ( 115 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

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
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('29',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

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

thf('31',plain,(
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

thf('32',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) ) @ X26 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X27 @ ( k3_yellow19 @ X27 @ ( k2_struct_0 @ X27 ) @ X26 ) ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['37','38','41','44','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','52'])).

thf('54',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

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
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('65',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('66',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['63','64','65','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q1K5ZcA98D
% 0.13/0.36  % Computer   : n014.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 11:35:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 385 iterations in 0.116s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.55  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(t15_yellow19, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55             ( v1_subset_1 @
% 0.37/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( m1_subset_1 @
% 0.37/0.55               B @ 
% 0.37/0.55               ( k1_zfmisc_1 @
% 0.37/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.55           ( ( B ) =
% 0.37/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55                ( v1_subset_1 @
% 0.37/0.55                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.55                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55                ( m1_subset_1 @
% 0.37/0.55                  B @ 
% 0.37/0.55                  ( k1_zfmisc_1 @
% 0.37/0.55                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.55              ( ( B ) =
% 0.37/0.55                ( k2_yellow19 @
% 0.37/0.56                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.37/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d3_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X23 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf(l27_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ (k1_tarski @ X15) @ X16) | (r2_hidden @ X15 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.56  thf(t1_mcart_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X22 : $i]:
% 0.37/0.56         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X22) @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.37/0.56  thf(t4_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.37/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.56  thf(t12_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.37/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 0.37/0.56          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0)
% 0.37/0.56          | ((k1_setfam_1 @ (k2_tarski @ (k1_tarski @ X1) @ X0))
% 0.37/0.56              = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.37/0.56  thf(commutativity_k2_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i]:
% 0.37/0.56         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.56           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.37/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.37/0.56            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.37/0.56          | (r2_hidden @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['8', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i]:
% 0.37/0.56         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.56  thf(t48_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.56           = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.56           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf(t4_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['15', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.56           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.37/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf(t3_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.56  thf('24', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.56  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.37/0.56          | (r2_hidden @ X1 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((sk_B_2)
% 0.37/0.56         != (k2_yellow19 @ sk_A @ 
% 0.37/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d2_yellow_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(t14_yellow19, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( m1_subset_1 @
% 0.37/0.56               B @ 
% 0.37/0.56               ( k1_zfmisc_1 @
% 0.37/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.56           ( ( k7_subset_1 @
% 0.37/0.56               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.37/0.56               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.37/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X26 : $i, X27 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X26)
% 0.37/0.56          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.37/0.56          | ~ (m1_subset_1 @ X26 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))))
% 0.37/0.56          | ((k7_subset_1 @ 
% 0.37/0.56              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27))) @ X26 @ 
% 0.37/0.56              (k1_tarski @ k1_xboole_0))
% 0.37/0.56              = (k2_yellow19 @ X27 @ 
% 0.37/0.56                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.37/0.56          | ~ (l1_struct_0 @ X27)
% 0.37/0.56          | (v2_struct_0 @ X27))),
% 0.37/0.56      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X26 : $i, X27 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X26)
% 0.37/0.56          | ~ (v2_waybel_0 @ X26 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.37/0.56          | ~ (v13_waybel_0 @ X26 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.37/0.56          | ~ (m1_subset_1 @ X26 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ 
% 0.37/0.56                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))))
% 0.37/0.56          | ((k7_subset_1 @ 
% 0.37/0.56              (u1_struct_0 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27)))) @ 
% 0.37/0.56              X26 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.56              = (k2_yellow19 @ X27 @ 
% 0.37/0.56                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.37/0.56          | ~ (l1_struct_0 @ X27)
% 0.37/0.56          | (v2_struct_0 @ X27))),
% 0.37/0.56      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | ((k7_subset_1 @ 
% 0.37/0.56            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.56            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.37/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.37/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56        | (v1_xboole_0 @ sk_B_2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '36'])).
% 0.37/0.56  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.37/0.56          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k7_subset_1 @ 
% 0.37/0.56           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.56           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B_2 @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B_2 @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56        | (v1_xboole_0 @ sk_B_2))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '38', '41', '44', '47'])).
% 0.37/0.56  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B_2)
% 0.37/0.56        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.37/0.56      inference('clc', [status(thm)], ['48', '49'])).
% 0.37/0.56  thf('51', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.56         = (k2_yellow19 @ sk_A @ 
% 0.37/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.37/0.56      inference('clc', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['26', '53'])).
% 0.37/0.56  thf('55', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.37/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(t2_yellow19, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.37/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.37/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.37/0.56             ( m1_subset_1 @
% 0.37/0.56               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.37/0.56           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X28)
% 0.37/0.56          | ~ (v1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X29)))
% 0.37/0.56          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.37/0.56          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.37/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X29))))
% 0.37/0.56          | ~ (r2_hidden @ X30 @ X28)
% 0.37/0.56          | ~ (v1_xboole_0 @ X30)
% 0.37/0.56          | (v1_xboole_0 @ X29))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X28)
% 0.37/0.56          | ~ (v1_subset_1 @ X28 @ 
% 0.37/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29))))
% 0.37/0.56          | ~ (v2_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.37/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))))
% 0.37/0.56          | ~ (r2_hidden @ X30 @ X28)
% 0.37/0.56          | ~ (v1_xboole_0 @ X30)
% 0.37/0.56          | (v1_xboole_0 @ X29))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (v1_xboole_0 @ X0)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.37/0.56               (u1_struct_0 @ 
% 0.37/0.56                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B_2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['56', '62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B_2 @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B_2 @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X25 : $i]: ((k3_yellow_1 @ X25) = (k3_lattice3 @ (k1_lattice3 @ X25)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B_2 @ 
% 0.37/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (v1_xboole_0 @ X0)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.37/0.56          | (v1_xboole_0 @ sk_B_2))),
% 0.37/0.56      inference('demod', [status(thm)], ['63', '64', '65', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B_2)
% 0.37/0.56        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['55', '69'])).
% 0.37/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.56  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.56  thf('73', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('74', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['1', '74'])).
% 0.37/0.56  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf(fc2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X24 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (v2_struct_0 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('79', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.56  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('81', plain, ((v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.56  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
