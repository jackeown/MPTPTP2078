%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M2dGV6kNIt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 170 expanded)
%              Number of leaves         :   43 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  890 (2168 expanded)
%              Number of equality atoms :   49 (  98 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('19',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) ) @ X29 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X30 @ ( k3_yellow19 @ X30 @ ( k2_struct_0 @ X30 ) @ X29 ) ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('22',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) ) @ X29 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X30 @ ( k3_yellow19 @ X30 @ ( k2_struct_0 @ X30 ) @ X29 ) ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['27','28','31','34','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','42'])).

thf('44',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['16','43'])).

thf('45',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_yellow_1 @ X32 ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X32 ) ) ) )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('48',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('51',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ) )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('55',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('56',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['53','54','55','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M2dGV6kNIt
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 98 iterations in 0.048s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.51  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(t15_yellow19, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51             ( v1_subset_1 @
% 0.21/0.51               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.51             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51             ( m1_subset_1 @
% 0.21/0.51               B @ 
% 0.21/0.51               ( k1_zfmisc_1 @
% 0.21/0.51                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.51           ( ( B ) =
% 0.21/0.51             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51                ( v1_subset_1 @
% 0.21/0.51                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.51                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51                ( m1_subset_1 @
% 0.21/0.51                  B @ 
% 0.21/0.51                  ( k1_zfmisc_1 @
% 0.21/0.51                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.51              ( ( B ) =
% 0.21/0.51                ( k2_yellow19 @
% 0.21/0.51                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X26 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf(l27_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ (k1_tarski @ X15) @ X16) | (r2_hidden @ X15 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.51  thf(t6_mcart_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.51                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.51                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.51                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.51                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.51                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X20) @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.51  thf(t4_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.21/0.51          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X1 @ X0)
% 0.21/0.51          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf(t100_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X9 @ X10)
% 0.21/0.51           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.21/0.51            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf(t4_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.51  thf(t98_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X13 @ X14)
% 0.21/0.51           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t1_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('14', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.51  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.21/0.51          | (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((sk_B_2)
% 0.21/0.51         != (k2_yellow19 @ sk_A @ 
% 0.21/0.51             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_yellow_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf(t14_yellow19, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.51             ( m1_subset_1 @
% 0.21/0.51               B @ 
% 0.21/0.51               ( k1_zfmisc_1 @
% 0.21/0.51                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.51           ( ( k7_subset_1 @
% 0.21/0.51               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.51               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.51             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X29)
% 0.21/0.51          | ~ (v2_waybel_0 @ X29 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))
% 0.21/0.51          | ~ (v13_waybel_0 @ X29 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))))
% 0.21/0.51          | ((k7_subset_1 @ 
% 0.21/0.51              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X30))) @ X29 @ 
% 0.21/0.51              (k1_tarski @ k1_xboole_0))
% 0.21/0.51              = (k2_yellow19 @ X30 @ 
% 0.21/0.51                 (k3_yellow19 @ X30 @ (k2_struct_0 @ X30) @ X29)))
% 0.21/0.51          | ~ (l1_struct_0 @ X30)
% 0.21/0.51          | (v2_struct_0 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X29)
% 0.21/0.51          | ~ (v2_waybel_0 @ X29 @ 
% 0.21/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30))))
% 0.21/0.51          | ~ (v13_waybel_0 @ X29 @ 
% 0.21/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30))))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (u1_struct_0 @ 
% 0.21/0.51                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30))))))
% 0.21/0.51          | ((k7_subset_1 @ 
% 0.21/0.51              (u1_struct_0 @ 
% 0.21/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30)))) @ 
% 0.21/0.51              X29 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.51              = (k2_yellow19 @ X30 @ 
% 0.21/0.51                 (k3_yellow19 @ X30 @ (k2_struct_0 @ X30) @ X29)))
% 0.21/0.51          | ~ (l1_struct_0 @ X30)
% 0.21/0.51          | (v2_struct_0 @ X30))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.51        | ((k7_subset_1 @ 
% 0.21/0.51            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.51            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.51            = (k2_yellow19 @ sk_A @ 
% 0.21/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.51        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.51             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.51        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.51             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '26'])).
% 0.21/0.51  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.21/0.51          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_subset_1 @ 
% 0.21/0.51           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.51           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.51            = (k2_yellow19 @ sk_A @ 
% 0.21/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28', '31', '34', '37'])).
% 0.21/0.51  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.51        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.51            = (k2_yellow19 @ sk_A @ 
% 0.21/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.21/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.51         = (k2_yellow19 @ sk_A @ 
% 0.21/0.51            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.51      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '43'])).
% 0.21/0.51  thf('45', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.21/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf(t2_yellow19, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.51             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.51             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.51             ( m1_subset_1 @
% 0.21/0.51               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.51           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X31)
% 0.21/0.51          | ~ (v1_subset_1 @ X31 @ (u1_struct_0 @ (k3_yellow_1 @ X32)))
% 0.21/0.51          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ X32))
% 0.21/0.51          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ X32))
% 0.21/0.51          | ~ (m1_subset_1 @ X31 @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X32))))
% 0.21/0.51          | ~ (r2_hidden @ X33 @ X31)
% 0.21/0.51          | ~ (v1_xboole_0 @ X33)
% 0.21/0.51          | (v1_xboole_0 @ X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X31)
% 0.21/0.51          | ~ (v1_subset_1 @ X31 @ 
% 0.21/0.51               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X32))))
% 0.21/0.51          | ~ (v2_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 0.21/0.51          | ~ (v13_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 0.21/0.51          | ~ (m1_subset_1 @ X31 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X32)))))
% 0.21/0.51          | ~ (r2_hidden @ X33 @ X31)
% 0.21/0.51          | ~ (v1_xboole_0 @ X33)
% 0.21/0.51          | (v1_xboole_0 @ X32))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.51          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.51          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.51          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.21/0.51               (u1_struct_0 @ 
% 0.21/0.51                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.51          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.51        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.51          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '54', '55', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.51        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '59'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '64'])).
% 0.21/0.51  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X27 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.21/0.51          | ~ (l1_struct_0 @ X27)
% 0.21/0.51          | (v2_struct_0 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('69', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('71', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
