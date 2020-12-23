%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxI4bA5DiS

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:42 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 452 expanded)
%              Number of leaves         :   50 ( 163 expanded)
%              Depth                    :   26
%              Number of atoms          : 1597 (4816 expanded)
%              Number of equality atoms :   78 ( 215 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v2_waybel_0 @ X40 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) )
      | ~ ( v13_waybel_0 @ X40 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X41 ) ) ) @ X40 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X41 @ ( k3_yellow19 @ X41 @ ( k2_struct_0 @ X41 ) @ X40 ) ) )
      | ~ ( l1_struct_0 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('5',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('6',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('7',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('8',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( v2_waybel_0 @ X40 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) )
      | ~ ( v13_waybel_0 @ X40 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X41 ) ) ) ) @ X40 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X41 @ ( k3_yellow19 @ X41 @ ( k2_struct_0 @ X41 ) @ X40 ) ) )
      | ~ ( l1_struct_0 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','26'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X27 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X33 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( r1_tarski @ X28 @ X26 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('42',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','26'])).

thf('71',plain,
    ( ( sk_B_1
     != ( k4_xboole_0 @ sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

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

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('73',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
      | ( ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
      | ( ( sk_C_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

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

thf('82',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( v1_subset_1 @ X42 @ ( u1_struct_0 @ ( k3_yellow_1 @ X43 ) ) )
      | ~ ( v2_waybel_0 @ X42 @ ( k3_yellow_1 @ X43 ) )
      | ~ ( v13_waybel_0 @ X42 @ ( k3_yellow_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X43 ) ) ) )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ~ ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('83',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('87',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( v1_subset_1 @ X42 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) ) )
      | ~ ( v2_waybel_0 @ X42 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) )
      | ~ ( v13_waybel_0 @ X42 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X43 ) ) ) ) )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ~ ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('90',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('91',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X39: $i] :
      ( ( k3_yellow_1 @ X39 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('93',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['88','89','90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['78','101'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('103',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('110',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','112'])).

thf('114',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,
    ( ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    r1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('119',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('120',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
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

thf('126',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('130',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('131',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('133',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','134'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('136',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['128','137'])).

thf('139',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','138'])).

thf('140',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('143',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('154',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('157',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['27','140','163'])).

thf('165',plain,(
    $false ),
    inference(simplify,[status(thm)],['164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JxI4bA5DiS
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 2.99/3.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.99/3.19  % Solved by: fo/fo7.sh
% 2.99/3.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.99/3.19  % done 4641 iterations in 2.736s
% 2.99/3.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.99/3.19  % SZS output start Refutation
% 2.99/3.19  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 2.99/3.19  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 2.99/3.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.99/3.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.99/3.19  thf(sk_A_type, type, sk_A: $i).
% 2.99/3.19  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 2.99/3.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.99/3.19  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.99/3.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 2.99/3.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.99/3.19  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.99/3.19  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.99/3.19  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.99/3.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.99/3.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.99/3.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.99/3.19  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 2.99/3.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.99/3.19  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 2.99/3.19  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 2.99/3.19  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.99/3.19  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.99/3.19  thf(sk_B_type, type, sk_B: $i > $i).
% 2.99/3.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.99/3.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 2.99/3.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.99/3.19  thf(t15_yellow19, conjecture,
% 2.99/3.19    (![A:$i]:
% 2.99/3.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.99/3.19       ( ![B:$i]:
% 2.99/3.19         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.99/3.19             ( v1_subset_1 @
% 2.99/3.19               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 2.99/3.19             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19             ( m1_subset_1 @
% 2.99/3.19               B @ 
% 2.99/3.19               ( k1_zfmisc_1 @
% 2.99/3.19                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.99/3.19           ( ( B ) =
% 2.99/3.19             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.99/3.19  thf(zf_stmt_0, negated_conjecture,
% 2.99/3.19    (~( ![A:$i]:
% 2.99/3.19        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.99/3.19          ( ![B:$i]:
% 2.99/3.19            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.99/3.19                ( v1_subset_1 @
% 2.99/3.19                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 2.99/3.19                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19                ( m1_subset_1 @
% 2.99/3.19                  B @ 
% 2.99/3.19                  ( k1_zfmisc_1 @
% 2.99/3.19                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.99/3.19              ( ( B ) =
% 2.99/3.19                ( k2_yellow19 @
% 2.99/3.19                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 2.99/3.19    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 2.99/3.19  thf('0', plain,
% 2.99/3.19      (((sk_B_1)
% 2.99/3.19         != (k2_yellow19 @ sk_A @ 
% 2.99/3.19             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('1', plain,
% 2.99/3.19      ((m1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf(d2_yellow_1, axiom,
% 2.99/3.19    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 2.99/3.19  thf('2', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('3', plain,
% 2.99/3.19      ((m1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (k1_zfmisc_1 @ 
% 2.99/3.19         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 2.99/3.19      inference('demod', [status(thm)], ['1', '2'])).
% 2.99/3.19  thf(t14_yellow19, axiom,
% 2.99/3.19    (![A:$i]:
% 2.99/3.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.99/3.19       ( ![B:$i]:
% 2.99/3.19         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.99/3.19             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.99/3.19             ( m1_subset_1 @
% 2.99/3.19               B @ 
% 2.99/3.19               ( k1_zfmisc_1 @
% 2.99/3.19                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.99/3.19           ( ( k7_subset_1 @
% 2.99/3.19               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 2.99/3.19               ( k1_tarski @ k1_xboole_0 ) ) =
% 2.99/3.19             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.99/3.19  thf('4', plain,
% 2.99/3.19      (![X40 : $i, X41 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ X40)
% 2.99/3.19          | ~ (v2_waybel_0 @ X40 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))
% 2.99/3.19          | ~ (v13_waybel_0 @ X40 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))
% 2.99/3.19          | ~ (m1_subset_1 @ X40 @ 
% 2.99/3.19               (k1_zfmisc_1 @ 
% 2.99/3.19                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X41)))))
% 2.99/3.19          | ((k7_subset_1 @ 
% 2.99/3.19              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X41))) @ X40 @ 
% 2.99/3.19              (k1_tarski @ k1_xboole_0))
% 2.99/3.19              = (k2_yellow19 @ X41 @ 
% 2.99/3.19                 (k3_yellow19 @ X41 @ (k2_struct_0 @ X41) @ X40)))
% 2.99/3.19          | ~ (l1_struct_0 @ X41)
% 2.99/3.19          | (v2_struct_0 @ X41))),
% 2.99/3.19      inference('cnf', [status(esa)], [t14_yellow19])).
% 2.99/3.19  thf('5', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('6', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('7', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('8', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('9', plain,
% 2.99/3.19      (![X40 : $i, X41 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ X40)
% 2.99/3.19          | ~ (v2_waybel_0 @ X40 @ 
% 2.99/3.19               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))
% 2.99/3.19          | ~ (v13_waybel_0 @ X40 @ 
% 2.99/3.19               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))
% 2.99/3.19          | ~ (m1_subset_1 @ X40 @ 
% 2.99/3.19               (k1_zfmisc_1 @ 
% 2.99/3.19                (u1_struct_0 @ 
% 2.99/3.19                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41))))))
% 2.99/3.19          | ((k7_subset_1 @ 
% 2.99/3.19              (u1_struct_0 @ 
% 2.99/3.19               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X41)))) @ 
% 2.99/3.19              X40 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19              = (k2_yellow19 @ X41 @ 
% 2.99/3.19                 (k3_yellow19 @ X41 @ (k2_struct_0 @ X41) @ X40)))
% 2.99/3.19          | ~ (l1_struct_0 @ X41)
% 2.99/3.19          | (v2_struct_0 @ X41))),
% 2.99/3.19      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 2.99/3.19  thf('10', plain,
% 2.99/3.19      (((v2_struct_0 @ sk_A)
% 2.99/3.19        | ~ (l1_struct_0 @ sk_A)
% 2.99/3.19        | ((k7_subset_1 @ 
% 2.99/3.19            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 2.99/3.19            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19            = (k2_yellow19 @ sk_A @ 
% 2.99/3.19               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.99/3.19        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 2.99/3.19             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.99/3.19        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 2.99/3.19             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.99/3.19        | (v1_xboole_0 @ sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['3', '9'])).
% 2.99/3.19  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('12', plain,
% 2.99/3.19      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('13', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('14', plain,
% 2.99/3.19      ((v13_waybel_0 @ sk_B_1 @ 
% 2.99/3.19        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.99/3.19      inference('demod', [status(thm)], ['12', '13'])).
% 2.99/3.19  thf('15', plain,
% 2.99/3.19      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('16', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('17', plain,
% 2.99/3.19      ((v2_waybel_0 @ sk_B_1 @ 
% 2.99/3.19        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.99/3.19      inference('demod', [status(thm)], ['15', '16'])).
% 2.99/3.19  thf('18', plain,
% 2.99/3.19      (((v2_struct_0 @ sk_A)
% 2.99/3.19        | ((k7_subset_1 @ 
% 2.99/3.19            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 2.99/3.19            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19            = (k2_yellow19 @ sk_A @ 
% 2.99/3.19               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.99/3.19        | (v1_xboole_0 @ sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['10', '11', '14', '17'])).
% 2.99/3.19  thf('19', plain,
% 2.99/3.19      ((m1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (k1_zfmisc_1 @ 
% 2.99/3.19         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 2.99/3.19      inference('demod', [status(thm)], ['1', '2'])).
% 2.99/3.19  thf(redefinition_k7_subset_1, axiom,
% 2.99/3.19    (![A:$i,B:$i,C:$i]:
% 2.99/3.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.99/3.19       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.99/3.19  thf('20', plain,
% 2.99/3.19      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.99/3.19         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 2.99/3.19          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 2.99/3.19      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.99/3.19  thf('21', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((k7_subset_1 @ 
% 2.99/3.19           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 2.99/3.19           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['19', '20'])).
% 2.99/3.19  thf('22', plain,
% 2.99/3.19      (((v2_struct_0 @ sk_A)
% 2.99/3.19        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19            = (k2_yellow19 @ sk_A @ 
% 2.99/3.19               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.99/3.19        | (v1_xboole_0 @ sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['18', '21'])).
% 2.99/3.19  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('24', plain,
% 2.99/3.19      (((v1_xboole_0 @ sk_B_1)
% 2.99/3.19        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19            = (k2_yellow19 @ sk_A @ 
% 2.99/3.19               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 2.99/3.19      inference('clc', [status(thm)], ['22', '23'])).
% 2.99/3.19  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('26', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19         = (k2_yellow19 @ sk_A @ 
% 2.99/3.19            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.99/3.19      inference('clc', [status(thm)], ['24', '25'])).
% 2.99/3.19  thf('27', plain,
% 2.99/3.19      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('demod', [status(thm)], ['0', '26'])).
% 2.99/3.19  thf(d1_xboole_0, axiom,
% 2.99/3.19    (![A:$i]:
% 2.99/3.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.99/3.19  thf('28', plain,
% 2.99/3.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.99/3.19  thf(d10_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.99/3.19  thf('29', plain,
% 2.99/3.19      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.99/3.19  thf('30', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 2.99/3.19      inference('simplify', [status(thm)], ['29'])).
% 2.99/3.19  thf(d1_zfmisc_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.99/3.19       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.99/3.19  thf('31', plain,
% 2.99/3.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.99/3.19         (~ (r1_tarski @ X25 @ X26)
% 2.99/3.19          | (r2_hidden @ X25 @ X27)
% 2.99/3.19          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.99/3.19  thf('32', plain,
% 2.99/3.19      (![X25 : $i, X26 : $i]:
% 2.99/3.19         ((r2_hidden @ X25 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X25 @ X26))),
% 2.99/3.19      inference('simplify', [status(thm)], ['31'])).
% 2.99/3.19  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['30', '32'])).
% 2.99/3.19  thf(t63_subset_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( r2_hidden @ A @ B ) =>
% 2.99/3.19       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.99/3.19  thf('34', plain,
% 2.99/3.19      (![X33 : $i, X34 : $i]:
% 2.99/3.19         ((m1_subset_1 @ (k1_tarski @ X33) @ (k1_zfmisc_1 @ X34))
% 2.99/3.19          | ~ (r2_hidden @ X33 @ X34))),
% 2.99/3.19      inference('cnf', [status(esa)], [t63_subset_1])).
% 2.99/3.19  thf('35', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['33', '34'])).
% 2.99/3.19  thf(t3_subset, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.99/3.19  thf('36', plain,
% 2.99/3.19      (![X35 : $i, X36 : $i]:
% 2.99/3.19         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_subset])).
% 2.99/3.19  thf('37', plain,
% 2.99/3.19      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['35', '36'])).
% 2.99/3.19  thf(d3_tarski, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( r1_tarski @ A @ B ) <=>
% 2.99/3.19       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.99/3.19  thf('38', plain,
% 2.99/3.19      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X3 @ X4)
% 2.99/3.19          | (r2_hidden @ X3 @ X5)
% 2.99/3.19          | ~ (r1_tarski @ X4 @ X5))),
% 2.99/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.99/3.19  thf('39', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 2.99/3.19          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['37', '38'])).
% 2.99/3.19  thf('40', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.99/3.19          | (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['28', '39'])).
% 2.99/3.19  thf('41', plain,
% 2.99/3.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X28 @ X27)
% 2.99/3.19          | (r1_tarski @ X28 @ X26)
% 2.99/3.19          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.99/3.19  thf('42', plain,
% 2.99/3.19      (![X26 : $i, X28 : $i]:
% 2.99/3.19         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 2.99/3.19      inference('simplify', [status(thm)], ['41'])).
% 2.99/3.19  thf('43', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.99/3.19          | (r1_tarski @ (sk_B @ (k1_tarski @ X0)) @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['40', '42'])).
% 2.99/3.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.99/3.19  thf('44', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.99/3.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.99/3.19  thf('45', plain,
% 2.99/3.19      (![X15 : $i, X17 : $i]:
% 2.99/3.19         (((X15) = (X17))
% 2.99/3.19          | ~ (r1_tarski @ X17 @ X15)
% 2.99/3.19          | ~ (r1_tarski @ X15 @ X17))),
% 2.99/3.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.99/3.19  thf('46', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['44', '45'])).
% 2.99/3.19  thf('47', plain,
% 2.99/3.19      (((v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | ((sk_B @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['43', '46'])).
% 2.99/3.19  thf('48', plain,
% 2.99/3.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.99/3.19  thf('49', plain,
% 2.99/3.19      (((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | (v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | (v1_xboole_0 @ (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('sup+', [status(thm)], ['47', '48'])).
% 2.99/3.19  thf('50', plain,
% 2.99/3.19      (((v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | (r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('simplify', [status(thm)], ['49'])).
% 2.99/3.19  thf('51', plain,
% 2.99/3.19      (![X4 : $i, X6 : $i]:
% 2.99/3.19         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.99/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.99/3.19  thf('52', plain,
% 2.99/3.19      (![X26 : $i, X28 : $i]:
% 2.99/3.19         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 2.99/3.19      inference('simplify', [status(thm)], ['41'])).
% 2.99/3.19  thf('53', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 2.99/3.19          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['51', '52'])).
% 2.99/3.19  thf('54', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['44', '45'])).
% 2.99/3.19  thf('55', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)
% 2.99/3.19          | ((sk_C @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['53', '54'])).
% 2.99/3.19  thf('56', plain,
% 2.99/3.19      (![X4 : $i, X6 : $i]:
% 2.99/3.19         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 2.99/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.99/3.19  thf('57', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (r2_hidden @ k1_xboole_0 @ X0)
% 2.99/3.19          | (r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)
% 2.99/3.19          | (r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['55', '56'])).
% 2.99/3.19  thf('58', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)
% 2.99/3.19          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 2.99/3.19      inference('simplify', [status(thm)], ['57'])).
% 2.99/3.19  thf('59', plain,
% 2.99/3.19      (((v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | (r1_tarski @ (k1_zfmisc_1 @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['50', '58'])).
% 2.99/3.19  thf('60', plain,
% 2.99/3.19      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['35', '36'])).
% 2.99/3.19  thf('61', plain,
% 2.99/3.19      (![X15 : $i, X17 : $i]:
% 2.99/3.19         (((X15) = (X17))
% 2.99/3.19          | ~ (r1_tarski @ X17 @ X15)
% 2.99/3.19          | ~ (r1_tarski @ X15 @ X17))),
% 2.99/3.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.99/3.19  thf('62', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (r1_tarski @ (k1_zfmisc_1 @ X0) @ (k1_tarski @ X0))
% 2.99/3.19          | ((k1_zfmisc_1 @ X0) = (k1_tarski @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['60', '61'])).
% 2.99/3.19  thf('63', plain,
% 2.99/3.19      (((v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['59', '62'])).
% 2.99/3.19  thf('64', plain,
% 2.99/3.19      (![X4 : $i, X6 : $i]:
% 2.99/3.19         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.99/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.99/3.19  thf('65', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.99/3.19  thf('66', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['64', '65'])).
% 2.99/3.19  thf('67', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['44', '45'])).
% 2.99/3.19  thf('68', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['66', '67'])).
% 2.99/3.19  thf('69', plain,
% 2.99/3.19      ((((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))
% 2.99/3.19        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['63', '68'])).
% 2.99/3.19  thf('70', plain,
% 2.99/3.19      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 2.99/3.19      inference('demod', [status(thm)], ['0', '26'])).
% 2.99/3.19  thf('71', plain,
% 2.99/3.19      ((((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.99/3.19        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['69', '70'])).
% 2.99/3.19  thf(t3_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.99/3.19            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.99/3.19       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.99/3.19            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.99/3.19  thf('72', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('73', plain,
% 2.99/3.19      (![X26 : $i, X28 : $i]:
% 2.99/3.19         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 2.99/3.19      inference('simplify', [status(thm)], ['41'])).
% 2.99/3.19  thf('74', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)
% 2.99/3.19          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['72', '73'])).
% 2.99/3.19  thf('75', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['44', '45'])).
% 2.99/3.19  thf('76', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)
% 2.99/3.19          | ((sk_C_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['74', '75'])).
% 2.99/3.19  thf('77', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('78', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['66', '67'])).
% 2.99/3.19  thf('79', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)
% 2.99/3.19          | ((sk_C_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['74', '75'])).
% 2.99/3.19  thf('80', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('81', plain,
% 2.99/3.19      ((m1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (k1_zfmisc_1 @ 
% 2.99/3.19         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 2.99/3.19      inference('demod', [status(thm)], ['1', '2'])).
% 2.99/3.19  thf(t2_yellow19, axiom,
% 2.99/3.19    (![A:$i]:
% 2.99/3.19     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.99/3.19       ( ![B:$i]:
% 2.99/3.19         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.99/3.19             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 2.99/3.19             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 2.99/3.19             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 2.99/3.19             ( m1_subset_1 @
% 2.99/3.19               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 2.99/3.19           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 2.99/3.19  thf('82', plain,
% 2.99/3.19      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ X42)
% 2.99/3.19          | ~ (v1_subset_1 @ X42 @ (u1_struct_0 @ (k3_yellow_1 @ X43)))
% 2.99/3.19          | ~ (v2_waybel_0 @ X42 @ (k3_yellow_1 @ X43))
% 2.99/3.19          | ~ (v13_waybel_0 @ X42 @ (k3_yellow_1 @ X43))
% 2.99/3.19          | ~ (m1_subset_1 @ X42 @ 
% 2.99/3.19               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X43))))
% 2.99/3.19          | ~ (r2_hidden @ X44 @ X42)
% 2.99/3.19          | ~ (v1_xboole_0 @ X44)
% 2.99/3.19          | (v1_xboole_0 @ X43))),
% 2.99/3.19      inference('cnf', [status(esa)], [t2_yellow19])).
% 2.99/3.19  thf('83', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('84', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('85', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('86', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('87', plain,
% 2.99/3.19      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ X42)
% 2.99/3.19          | ~ (v1_subset_1 @ X42 @ 
% 2.99/3.19               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X43))))
% 2.99/3.19          | ~ (v2_waybel_0 @ X42 @ (k3_lattice3 @ (k1_lattice3 @ X43)))
% 2.99/3.19          | ~ (v13_waybel_0 @ X42 @ (k3_lattice3 @ (k1_lattice3 @ X43)))
% 2.99/3.19          | ~ (m1_subset_1 @ X42 @ 
% 2.99/3.19               (k1_zfmisc_1 @ 
% 2.99/3.19                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X43)))))
% 2.99/3.19          | ~ (r2_hidden @ X44 @ X42)
% 2.99/3.19          | ~ (v1_xboole_0 @ X44)
% 2.99/3.19          | (v1_xboole_0 @ X43))),
% 2.99/3.19      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 2.99/3.19  thf('88', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.99/3.19          | ~ (v1_xboole_0 @ X0)
% 2.99/3.19          | ~ (r2_hidden @ X0 @ sk_B_1)
% 2.99/3.19          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 2.99/3.19               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.99/3.19          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 2.99/3.19               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.99/3.19          | ~ (v1_subset_1 @ sk_B_1 @ 
% 2.99/3.19               (u1_struct_0 @ 
% 2.99/3.19                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 2.99/3.19          | (v1_xboole_0 @ sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['81', '87'])).
% 2.99/3.19  thf('89', plain,
% 2.99/3.19      ((v13_waybel_0 @ sk_B_1 @ 
% 2.99/3.19        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.99/3.19      inference('demod', [status(thm)], ['12', '13'])).
% 2.99/3.19  thf('90', plain,
% 2.99/3.19      ((v2_waybel_0 @ sk_B_1 @ 
% 2.99/3.19        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.99/3.19      inference('demod', [status(thm)], ['15', '16'])).
% 2.99/3.19  thf('91', plain,
% 2.99/3.19      ((v1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('92', plain,
% 2.99/3.19      (![X39 : $i]: ((k3_yellow_1 @ X39) = (k3_lattice3 @ (k1_lattice3 @ X39)))),
% 2.99/3.19      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.99/3.19  thf('93', plain,
% 2.99/3.19      ((v1_subset_1 @ sk_B_1 @ 
% 2.99/3.19        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 2.99/3.19      inference('demod', [status(thm)], ['91', '92'])).
% 2.99/3.19  thf('94', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.99/3.19          | ~ (v1_xboole_0 @ X0)
% 2.99/3.19          | ~ (r2_hidden @ X0 @ sk_B_1)
% 2.99/3.19          | (v1_xboole_0 @ sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['88', '89', '90', '93'])).
% 2.99/3.19  thf('95', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X0 @ sk_B_1)
% 2.99/3.19          | (v1_xboole_0 @ sk_B_1)
% 2.99/3.19          | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ X0))
% 2.99/3.19          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['80', '94'])).
% 2.99/3.19  thf('96', plain,
% 2.99/3.19      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)
% 2.99/3.19        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.99/3.19        | (v1_xboole_0 @ sk_B_1)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['79', '95'])).
% 2.99/3.19  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.99/3.19  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.99/3.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.99/3.19  thf('98', plain,
% 2.99/3.19      (((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)
% 2.99/3.19        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.99/3.19        | (v1_xboole_0 @ sk_B_1)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['96', '97'])).
% 2.99/3.19  thf('99', plain,
% 2.99/3.19      (((v1_xboole_0 @ sk_B_1)
% 2.99/3.19        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1))),
% 2.99/3.19      inference('simplify', [status(thm)], ['98'])).
% 2.99/3.19  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('101', plain,
% 2.99/3.19      (((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)
% 2.99/3.19        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.99/3.19      inference('clc', [status(thm)], ['99', '100'])).
% 2.99/3.19  thf('102', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ sk_B_1)
% 2.99/3.19          | ~ (v1_xboole_0 @ X0)
% 2.99/3.19          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.99/3.19      inference('sup+', [status(thm)], ['78', '101'])).
% 2.99/3.19  thf(fc5_struct_0, axiom,
% 2.99/3.19    (![A:$i]:
% 2.99/3.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.99/3.19       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 2.99/3.19  thf('103', plain,
% 2.99/3.19      (![X38 : $i]:
% 2.99/3.19         (~ (v1_xboole_0 @ (k2_struct_0 @ X38))
% 2.99/3.19          | ~ (l1_struct_0 @ X38)
% 2.99/3.19          | (v2_struct_0 @ X38))),
% 2.99/3.19      inference('cnf', [status(esa)], [fc5_struct_0])).
% 2.99/3.19  thf('104', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (v1_xboole_0 @ X0)
% 2.99/3.19          | (r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ sk_B_1)
% 2.99/3.19          | (v2_struct_0 @ sk_A)
% 2.99/3.19          | ~ (l1_struct_0 @ sk_A))),
% 2.99/3.19      inference('sup-', [status(thm)], ['102', '103'])).
% 2.99/3.19  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('106', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (v1_xboole_0 @ X0)
% 2.99/3.19          | (r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ sk_B_1)
% 2.99/3.19          | (v2_struct_0 @ sk_A))),
% 2.99/3.19      inference('demod', [status(thm)], ['104', '105'])).
% 2.99/3.19  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('108', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 2.99/3.19      inference('clc', [status(thm)], ['106', '107'])).
% 2.99/3.19  thf('109', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['30', '32'])).
% 2.99/3.19  thf('110', plain,
% 2.99/3.19      (![X7 : $i, X9 : $i, X10 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X9 @ X7)
% 2.99/3.19          | ~ (r2_hidden @ X9 @ X10)
% 2.99/3.19          | ~ (r1_xboole_0 @ X7 @ X10))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('111', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (~ (r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['109', '110'])).
% 2.99/3.19  thf('112', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['108', '111'])).
% 2.99/3.19  thf('113', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X0 @ sk_B_1)
% 2.99/3.19          | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['77', '112'])).
% 2.99/3.19  thf('114', plain,
% 2.99/3.19      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['76', '113'])).
% 2.99/3.19  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.99/3.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.99/3.19  thf('116', plain,
% 2.99/3.19      (((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)
% 2.99/3.19        | (r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['114', '115'])).
% 2.99/3.19  thf('117', plain, ((r1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0) @ sk_B_1)),
% 2.99/3.19      inference('simplify', [status(thm)], ['116'])).
% 2.99/3.19  thf('118', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('119', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('120', plain,
% 2.99/3.19      (![X7 : $i, X9 : $i, X10 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X9 @ X7)
% 2.99/3.19          | ~ (r2_hidden @ X9 @ X10)
% 2.99/3.19          | ~ (r1_xboole_0 @ X7 @ X10))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('121', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X1 @ X0)
% 2.99/3.19          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.99/3.19          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 2.99/3.19      inference('sup-', [status(thm)], ['119', '120'])).
% 2.99/3.19  thf('122', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X0 @ X1)
% 2.99/3.19          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.99/3.19          | (r1_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['118', '121'])).
% 2.99/3.19  thf('123', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('simplify', [status(thm)], ['122'])).
% 2.99/3.19  thf('124', plain, ((r1_xboole_0 @ sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['117', '123'])).
% 2.99/3.19  thf('125', plain,
% 2.99/3.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.99/3.19  thf(t4_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.99/3.19            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.99/3.19       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.99/3.19            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.99/3.19  thf('126', plain,
% 2.99/3.19      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 2.99/3.19          | ~ (r1_xboole_0 @ X11 @ X14))),
% 2.99/3.19      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.99/3.19  thf('127', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['125', '126'])).
% 2.99/3.19  thf('128', plain,
% 2.99/3.19      ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['124', '127'])).
% 2.99/3.19  thf('129', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['66', '67'])).
% 2.99/3.19  thf(t4_boole, axiom,
% 2.99/3.19    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.99/3.19  thf('130', plain,
% 2.99/3.19      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 2.99/3.19      inference('cnf', [status(esa)], [t4_boole])).
% 2.99/3.19  thf(t98_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.99/3.19  thf('131', plain,
% 2.99/3.19      (![X23 : $i, X24 : $i]:
% 2.99/3.19         ((k2_xboole_0 @ X23 @ X24)
% 2.99/3.19           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.99/3.19  thf('132', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['130', '131'])).
% 2.99/3.19  thf(t1_boole, axiom,
% 2.99/3.19    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.99/3.19  thf('133', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.99/3.19      inference('cnf', [status(esa)], [t1_boole])).
% 2.99/3.19  thf('134', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['132', '133'])).
% 2.99/3.19  thf('135', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['129', '134'])).
% 2.99/3.19  thf(t100_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.99/3.19  thf('136', plain,
% 2.99/3.19      (![X18 : $i, X19 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X18 @ X19)
% 2.99/3.19           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.99/3.19  thf('137', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 2.99/3.19          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.99/3.19      inference('sup+', [status(thm)], ['135', '136'])).
% 2.99/3.19  thf('138', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)) = (sk_B_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['128', '137'])).
% 2.99/3.19  thf('139', plain,
% 2.99/3.19      ((((sk_B_1) != (sk_B_1)) | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 2.99/3.19      inference('demod', [status(thm)], ['71', '138'])).
% 2.99/3.19  thf('140', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 2.99/3.19      inference('simplify', [status(thm)], ['139'])).
% 2.99/3.19  thf('141', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.99/3.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.99/3.19  thf('143', plain,
% 2.99/3.19      (![X7 : $i, X8 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('144', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.99/3.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.99/3.19  thf('145', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['143', '144'])).
% 2.99/3.19  thf('146', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.99/3.19      inference('sup-', [status(thm)], ['142', '145'])).
% 2.99/3.19  thf('147', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['125', '126'])).
% 2.99/3.19  thf('148', plain,
% 2.99/3.19      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['146', '147'])).
% 2.99/3.19  thf('149', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['66', '67'])).
% 2.99/3.19  thf('150', plain,
% 2.99/3.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['148', '149'])).
% 2.99/3.19  thf('151', plain,
% 2.99/3.19      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 2.99/3.19          | ~ (r1_xboole_0 @ X11 @ X14))),
% 2.99/3.19      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.99/3.19  thf('152', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['150', '151'])).
% 2.99/3.19  thf('153', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.99/3.19      inference('sup-', [status(thm)], ['142', '145'])).
% 2.99/3.19  thf('154', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.99/3.19      inference('demod', [status(thm)], ['152', '153'])).
% 2.99/3.19  thf('155', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.99/3.19      inference('sup-', [status(thm)], ['141', '154'])).
% 2.99/3.19  thf('156', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['125', '126'])).
% 2.99/3.19  thf('157', plain,
% 2.99/3.19      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['155', '156'])).
% 2.99/3.19  thf('158', plain,
% 2.99/3.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['66', '67'])).
% 2.99/3.19  thf('159', plain,
% 2.99/3.19      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['157', '158'])).
% 2.99/3.19  thf('160', plain,
% 2.99/3.19      (![X18 : $i, X19 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X18 @ X19)
% 2.99/3.19           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.99/3.19  thf('161', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['159', '160'])).
% 2.99/3.19  thf('162', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['132', '133'])).
% 2.99/3.19  thf('163', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.99/3.19      inference('demod', [status(thm)], ['161', '162'])).
% 2.99/3.19  thf('164', plain, (((sk_B_1) != (sk_B_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['27', '140', '163'])).
% 2.99/3.19  thf('165', plain, ($false), inference('simplify', [status(thm)], ['164'])).
% 2.99/3.19  
% 2.99/3.19  % SZS output end Refutation
% 2.99/3.19  
% 2.99/3.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
