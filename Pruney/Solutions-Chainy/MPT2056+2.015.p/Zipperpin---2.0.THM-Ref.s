%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XqCLUgOJxu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 163 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  866 (2068 expanded)
%              Number of equality atoms :   47 (  94 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('18',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['26','27','30','33','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','41'])).

thf('43',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['15','42'])).

thf('44',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('46',plain,(
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

thf('47',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('54',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('55',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['52','53','54','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XqCLUgOJxu
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 98 iterations in 0.040s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.50  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.50  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.50  thf(t15_yellow19, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50             ( v1_subset_1 @
% 0.20/0.50               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.50             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.50             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.50             ( m1_subset_1 @
% 0.20/0.50               B @ 
% 0.20/0.50               ( k1_zfmisc_1 @
% 0.20/0.50                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.50           ( ( B ) =
% 0.20/0.50             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50                ( v1_subset_1 @
% 0.20/0.50                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.50                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.50                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.50                ( m1_subset_1 @
% 0.20/0.50                  B @ 
% 0.20/0.50                  ( k1_zfmisc_1 @
% 0.20/0.50                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.50              ( ( B ) =
% 0.20/0.50                ( k2_yellow19 @
% 0.20/0.50                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l27_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k1_tarski @ X15) @ X16) | (r2_hidden @ X15 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.50  thf(t6_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.50                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.20/0.50                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.20/0.50                       ( r2_hidden @ G @ B ) ) =>
% 0.20/0.50                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X20) @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.20/0.50  thf(t4_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.50          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ X1 @ X0)
% 0.20/0.50          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.51  thf(t100_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X9 @ X10)
% 0.20/0.51           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.20/0.51            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.51  thf(t4_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.51  thf(t98_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.51           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(t1_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('13', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.51  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.20/0.51          | (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((sk_B_2)
% 0.20/0.51         != (k2_yellow19 @ sk_A @ 
% 0.20/0.51             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d2_yellow_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(t14_yellow19, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.51             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.51             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.51             ( m1_subset_1 @
% 0.20/0.51               B @ 
% 0.20/0.51               ( k1_zfmisc_1 @
% 0.20/0.51                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.51           ( ( k7_subset_1 @
% 0.20/0.51               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.20/0.51               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.20/0.51             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X28)
% 0.20/0.51          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.51          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.20/0.51          | ((k7_subset_1 @ 
% 0.20/0.51              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))) @ X28 @ 
% 0.20/0.51              (k1_tarski @ k1_xboole_0))
% 0.20/0.51              = (k2_yellow19 @ X29 @ 
% 0.20/0.51                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.51          | ~ (l1_struct_0 @ X29)
% 0.20/0.51          | (v2_struct_0 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X28)
% 0.20/0.51          | ~ (v2_waybel_0 @ X28 @ 
% 0.20/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.51          | ~ (v13_waybel_0 @ X28 @ 
% 0.20/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ 
% 0.20/0.51                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.20/0.51          | ((k7_subset_1 @ 
% 0.20/0.51              (u1_struct_0 @ 
% 0.20/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))) @ 
% 0.20/0.51              X28 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.51              = (k2_yellow19 @ X29 @ 
% 0.20/0.51                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.51          | ~ (l1_struct_0 @ X29)
% 0.20/0.51          | (v2_struct_0 @ X29))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.51        | ((k7_subset_1 @ 
% 0.20/0.51            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.51            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.51            = (k2_yellow19 @ sk_A @ 
% 0.20/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.20/0.51        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.51             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.51        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.51             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.51  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.20/0.51          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k7_subset_1 @ 
% 0.20/0.51           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.51           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.51            = (k2_yellow19 @ sk_A @ 
% 0.20/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.20/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '30', '33', '36'])).
% 0.20/0.51  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.51        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.51            = (k2_yellow19 @ sk_A @ 
% 0.20/0.51               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.20/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.51         = (k2_yellow19 @ sk_A @ 
% 0.20/0.51            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.20/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '42'])).
% 0.20/0.51  thf('44', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.20/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(t2_yellow19, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.51             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.51             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.51             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.51             ( m1_subset_1 @
% 0.20/0.51               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.51           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X30)
% 0.20/0.51          | ~ (v1_subset_1 @ X30 @ (u1_struct_0 @ (k3_yellow_1 @ X31)))
% 0.20/0.51          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.51          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.51          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X31))))
% 0.20/0.51          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.51          | ~ (v1_xboole_0 @ X32)
% 0.20/0.51          | (v1_xboole_0 @ X31))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X30)
% 0.20/0.51          | ~ (v1_subset_1 @ X30 @ 
% 0.20/0.51               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31))))
% 0.20/0.51          | ~ (v2_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.51          | ~ (v13_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.51          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31)))))
% 0.20/0.51          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.51          | ~ (v1_xboole_0 @ X32)
% 0.20/0.51          | (v1_xboole_0 @ X31))),
% 0.20/0.51      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.51          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.51          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.51               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.51          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.20/0.51               (u1_struct_0 @ 
% 0.20/0.51                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.51          | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((v13_waybel_0 @ sk_B_2 @ 
% 0.20/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((v2_waybel_0 @ sk_B_2 @ 
% 0.20/0.51        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((v1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((v1_subset_1 @ sk_B_2 @ 
% 0.20/0.51        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.51          | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.51      inference('demod', [status(thm)], ['52', '53', '54', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.51        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.51        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '58'])).
% 0.20/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.51  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.51  thf('62', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.51  thf(fc5_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 0.20/0.51          | ~ (l1_struct_0 @ X26)
% 0.20/0.51          | (v2_struct_0 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.20/0.51  thf('65', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
