%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBZ1lYApR9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 178 expanded)
%              Number of leaves         :   46 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  916 (2202 expanded)
%              Number of equality atoms :   50 ( 100 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X8 ) ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

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
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('23',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('26',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','32','35','38','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','46'])).

thf('48',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','47'])).

thf('49',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('51',plain,(
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

thf('52',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('59',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('60',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBZ1lYApR9
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 115 iterations in 0.056s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.52  thf(t15_yellow19, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( v1_subset_1 @
% 0.20/0.52               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52             ( m1_subset_1 @
% 0.20/0.52               B @ 
% 0.20/0.52               ( k1_zfmisc_1 @
% 0.20/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.52           ( ( B ) =
% 0.20/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52                ( v1_subset_1 @
% 0.20/0.52                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.52                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52                ( m1_subset_1 @
% 0.20/0.52                  B @ 
% 0.20/0.52                  ( k1_zfmisc_1 @
% 0.20/0.52                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.52              ( ( B ) =
% 0.20/0.52                ( k2_yellow19 @
% 0.20/0.52                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X25 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf(l27_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k1_tarski @ X17) @ X18) | (r2_hidden @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t1_mcart_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X24 : $i]:
% 0.20/0.52         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X24) @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.20/0.52  thf(t4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.52          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X7 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X8)))
% 0.20/0.52          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ X1)
% 0.20/0.52          | ((k1_setfam_1 @ (k2_tarski @ X1 @ (k1_tarski @ X0)))
% 0.20/0.52              = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X9 @ X10)
% 0.20/0.52           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X9 @ X10)
% 0.20/0.52           = (k5_xboole_0 @ X9 @ (k1_setfam_1 @ (k2_tarski @ X9 @ X10))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.20/0.52            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.52  thf(t4_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.52  thf(t98_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.52           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf(t1_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('18', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.20/0.52          | (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((sk_B_2)
% 0.20/0.52         != (k2_yellow19 @ sk_A @ 
% 0.20/0.52             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_yellow_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf(t14_yellow19, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.52             ( m1_subset_1 @
% 0.20/0.52               B @ 
% 0.20/0.52               ( k1_zfmisc_1 @
% 0.20/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.52           ( ( k7_subset_1 @
% 0.20/0.52               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.20/0.52               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.20/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X28)
% 0.20/0.52          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.52          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.52          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.20/0.52          | ((k7_subset_1 @ 
% 0.20/0.52              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))) @ X28 @ 
% 0.20/0.52              (k1_tarski @ k1_xboole_0))
% 0.20/0.52              = (k2_yellow19 @ X29 @ 
% 0.20/0.52                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.52          | ~ (l1_struct_0 @ X29)
% 0.20/0.52          | (v2_struct_0 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X28)
% 0.20/0.52          | ~ (v2_waybel_0 @ X28 @ 
% 0.20/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.52          | ~ (v13_waybel_0 @ X28 @ 
% 0.20/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.52          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (u1_struct_0 @ 
% 0.20/0.52                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.20/0.52          | ((k7_subset_1 @ 
% 0.20/0.52              (u1_struct_0 @ 
% 0.20/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))) @ 
% 0.20/0.52              X28 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.52              = (k2_yellow19 @ X29 @ 
% 0.20/0.52                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.52          | ~ (l1_struct_0 @ X29)
% 0.20/0.52          | (v2_struct_0 @ X29))),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52        | ((k7_subset_1 @ 
% 0.20/0.52            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.52            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.52            = (k2_yellow19 @ sk_A @ 
% 0.20/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.20/0.52        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.52             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.52        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.52             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '30'])).
% 0.20/0.52  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.20/0.52          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_subset_1 @ 
% 0.20/0.52           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.52           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.52            = (k2_yellow19 @ sk_A @ 
% 0.20/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['31', '32', '35', '38', '41'])).
% 0.20/0.52  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.52        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.52            = (k2_yellow19 @ sk_A @ 
% 0.20/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.20/0.52      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.52         = (k2_yellow19 @ sk_A @ 
% 0.20/0.52            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.20/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '47'])).
% 0.20/0.52  thf('49', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf(t2_yellow19, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.52             ( m1_subset_1 @
% 0.20/0.52               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.52           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X30)
% 0.20/0.52          | ~ (v1_subset_1 @ X30 @ (u1_struct_0 @ (k3_yellow_1 @ X31)))
% 0.20/0.52          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.52          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X31))))
% 0.20/0.52          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.52          | ~ (v1_xboole_0 @ X32)
% 0.20/0.52          | (v1_xboole_0 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X30)
% 0.20/0.52          | ~ (v1_subset_1 @ X30 @ 
% 0.20/0.52               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31))))
% 0.20/0.52          | ~ (v2_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.52          | ~ (v13_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31)))))
% 0.20/0.52          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.52          | ~ (v1_xboole_0 @ X32)
% 0.20/0.52          | (v1_xboole_0 @ X31))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.52          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.52          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.52          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.52          | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((v1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((v1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.52          | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58', '59', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.52        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '63'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['1', '68'])).
% 0.20/0.52  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf(fc2_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X26 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.20/0.52          | ~ (l1_struct_0 @ X26)
% 0.20/0.52          | (v2_struct_0 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.52  thf('73', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('75', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
