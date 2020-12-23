%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoHUlldJ3F

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 194 expanded)
%              Number of leaves         :   45 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  919 (2232 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('30',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

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

thf('32',plain,(
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
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','42','45','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','53'])).

thf('55',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

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
    inference(demod,[status(thm)],['43','44'])).

thf('66',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

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

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoHUlldJ3F
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 152 iterations in 0.092s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.55  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.22/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.22/0.55  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.22/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(t15_yellow19, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.55             ( v1_subset_1 @
% 0.22/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               B @ 
% 0.22/0.55               ( k1_zfmisc_1 @
% 0.22/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.55           ( ( B ) =
% 0.22/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.55                ( v1_subset_1 @
% 0.22/0.55                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.55                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55                ( m1_subset_1 @
% 0.22/0.55                  B @ 
% 0.22/0.55                  ( k1_zfmisc_1 @
% 0.22/0.55                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.55              ( ( B ) =
% 0.22/0.55                ( k2_yellow19 @
% 0.22/0.55                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.22/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(l27_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X21 : $i, X22 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ (k1_tarski @ X21) @ X22) | (r2_hidden @ X21 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf(d1_xboole_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.55  thf(t4_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.22/0.55          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ X0 @ X1)
% 0.22/0.55          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.55  thf(d3_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X4 : $i, X6 : $i]:
% 0.22/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.55  thf('11', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X13 : $i, X15 : $i]:
% 0.22/0.55         (((X13) = (X15))
% 0.22/0.55          | ~ (r1_tarski @ X15 @ X13)
% 0.22/0.55          | ~ (r1_tarski @ X13 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ X0 @ X1)
% 0.22/0.55          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['7', '14'])).
% 0.22/0.55  thf(t100_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X16 @ X17)
% 0.22/0.55           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.22/0.55            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.22/0.55          | (r2_hidden @ X0 @ X1))),
% 0.22/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.55  thf('18', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X16 @ X17)
% 0.22/0.55           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf(t3_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('25', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.55  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.22/0.55          | (r2_hidden @ X0 @ X1))),
% 0.22/0.55      inference('demod', [status(thm)], ['17', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (((sk_B_1)
% 0.22/0.55         != (k2_yellow19 @ sk_A @ 
% 0.22/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d2_yellow_1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf(t14_yellow19, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               B @ 
% 0.22/0.55               ( k1_zfmisc_1 @
% 0.22/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.55           ( ( k7_subset_1 @
% 0.22/0.55               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.22/0.55               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.22/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X28 : $i, X29 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X28)
% 0.22/0.55          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.22/0.55          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.22/0.55          | ~ (m1_subset_1 @ X28 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.22/0.55          | ((k7_subset_1 @ 
% 0.22/0.55              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))) @ X28 @ 
% 0.22/0.55              (k1_tarski @ k1_xboole_0))
% 0.22/0.55              = (k2_yellow19 @ X29 @ 
% 0.22/0.55                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.22/0.55          | ~ (l1_struct_0 @ X29)
% 0.22/0.55          | (v2_struct_0 @ X29))),
% 0.22/0.55      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X28 : $i, X29 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X28)
% 0.22/0.55          | ~ (v2_waybel_0 @ X28 @ 
% 0.22/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.22/0.55          | ~ (v13_waybel_0 @ X28 @ 
% 0.22/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.22/0.55          | ~ (m1_subset_1 @ X28 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (u1_struct_0 @ 
% 0.22/0.55                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.22/0.55          | ((k7_subset_1 @ 
% 0.22/0.55              (u1_struct_0 @ 
% 0.22/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))) @ 
% 0.22/0.55              X28 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.55              = (k2_yellow19 @ X29 @ 
% 0.22/0.55                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.22/0.55          | ~ (l1_struct_0 @ X29)
% 0.22/0.55          | (v2_struct_0 @ X29))),
% 0.22/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | ((k7_subset_1 @ 
% 0.22/0.55            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.55            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.55            = (k2_yellow19 @ sk_A @ 
% 0.22/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.22/0.55        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.55        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['31', '37'])).
% 0.22/0.55  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.22/0.55          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k7_subset_1 @ 
% 0.22/0.55           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.55           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.55            = (k2_yellow19 @ sk_A @ 
% 0.22/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.22/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.55      inference('demod', [status(thm)], ['38', '39', '42', '45', '48'])).
% 0.22/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.55        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.55            = (k2_yellow19 @ sk_A @ 
% 0.22/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('52', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.55         = (k2_yellow19 @ sk_A @ 
% 0.22/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['28', '53'])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '54'])).
% 0.22/0.55  thf('56', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.22/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf(t2_yellow19, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.55             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.22/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.22/0.55           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X30)
% 0.22/0.55          | ~ (v1_subset_1 @ X30 @ (u1_struct_0 @ (k3_yellow_1 @ X31)))
% 0.22/0.55          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.22/0.55          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.22/0.55          | ~ (m1_subset_1 @ X30 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X31))))
% 0.22/0.55          | ~ (r2_hidden @ X32 @ X30)
% 0.22/0.55          | ~ (v1_xboole_0 @ X32)
% 0.22/0.55          | (v1_xboole_0 @ X31))),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('61', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X30)
% 0.22/0.55          | ~ (v1_subset_1 @ X30 @ 
% 0.22/0.55               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31))))
% 0.22/0.55          | ~ (v2_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.22/0.55          | ~ (v13_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.22/0.55          | ~ (m1_subset_1 @ X30 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31)))))
% 0.22/0.55          | ~ (r2_hidden @ X32 @ X30)
% 0.22/0.55          | ~ (v1_xboole_0 @ X32)
% 0.22/0.55          | (v1_xboole_0 @ X31))),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.55          | ~ (v1_xboole_0 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.22/0.55          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.55          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.55          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.22/0.55               (u1_struct_0 @ 
% 0.22/0.55                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.22/0.55          | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '63'])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      ((v1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      ((v1_subset_1 @ sk_B_1 @ 
% 0.22/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.55          | ~ (v1_xboole_0 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.22/0.55          | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.55      inference('demod', [status(thm)], ['64', '65', '66', '69'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.55        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['56', '70'])).
% 0.22/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.55  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.22/0.55  thf('74', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('75', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf(fc5_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (![X26 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 0.22/0.55          | ~ (l1_struct_0 @ X26)
% 0.22/0.55          | (v2_struct_0 @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.55  thf('77', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.55  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.55  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
