%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bqp1qRUQTY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 169 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  856 (2116 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) ) @ X21 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X22 @ ( k3_yellow19 @ X22 @ ( k2_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) ) @ X21 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X22 @ ( k3_yellow19 @ X22 @ ( k2_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29','32','35','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','43'])).

thf('45',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','44'])).

thf('46',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ~ ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('49',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('51',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ) )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ~ ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('56',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bqp1qRUQTY
% 0.15/0.37  % Computer   : n020.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 50 iterations in 0.026s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.23/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.52  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.23/0.52  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.52  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.23/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.23/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.23/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.52  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.23/0.52  thf(t15_yellow19, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52             ( v1_subset_1 @
% 0.23/0.52               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.23/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52             ( m1_subset_1 @
% 0.23/0.52               B @ 
% 0.23/0.52               ( k1_zfmisc_1 @
% 0.23/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.52           ( ( B ) =
% 0.23/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52                ( v1_subset_1 @
% 0.23/0.52                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.23/0.52                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52                ( m1_subset_1 @
% 0.23/0.52                  B @ 
% 0.23/0.52                  ( k1_zfmisc_1 @
% 0.23/0.52                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.52              ( ( B ) =
% 0.23/0.52                ( k2_yellow19 @
% 0.23/0.52                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.23/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(l27_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ (k1_tarski @ X10) @ X11) | (r2_hidden @ X10 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.23/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.52  thf(t29_mcart_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.23/0.52                 ( ![C:$i,D:$i,E:$i]:
% 0.23/0.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.23/0.52                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X15 : $i]:
% 0.23/0.52         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.23/0.52      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.23/0.52  thf(t4_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.23/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r2_hidden @ X0 @ X1)
% 0.23/0.52          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.52  thf(t100_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.23/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.23/0.52            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ X0 @ X1))),
% 0.23/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.52  thf('10', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.23/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.23/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.23/0.52  thf(t3_boole, axiom,
% 0.23/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.52  thf('15', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.52  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.23/0.52          | (r2_hidden @ X0 @ X1))),
% 0.23/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (((sk_B_1)
% 0.23/0.52         != (k2_yellow19 @ sk_A @ 
% 0.23/0.52             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(d2_yellow_1, axiom,
% 0.23/0.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (k1_zfmisc_1 @ 
% 0.23/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf(t14_yellow19, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.23/0.52             ( m1_subset_1 @
% 0.23/0.52               B @ 
% 0.23/0.52               ( k1_zfmisc_1 @
% 0.23/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.23/0.52           ( ( k7_subset_1 @
% 0.23/0.52               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.23/0.52               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.23/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X21)
% 0.23/0.52          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))
% 0.23/0.52          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))
% 0.23/0.52          | ~ (m1_subset_1 @ X21 @ 
% 0.23/0.52               (k1_zfmisc_1 @ 
% 0.23/0.52                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))))
% 0.23/0.52          | ((k7_subset_1 @ 
% 0.23/0.52              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X22))) @ X21 @ 
% 0.23/0.52              (k1_tarski @ k1_xboole_0))
% 0.23/0.52              = (k2_yellow19 @ X22 @ 
% 0.23/0.52                 (k3_yellow19 @ X22 @ (k2_struct_0 @ X22) @ X21)))
% 0.23/0.52          | ~ (l1_struct_0 @ X22)
% 0.23/0.52          | (v2_struct_0 @ X22))),
% 0.23/0.52      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X21)
% 0.23/0.52          | ~ (v2_waybel_0 @ X21 @ 
% 0.23/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))
% 0.23/0.52          | ~ (v13_waybel_0 @ X21 @ 
% 0.23/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))
% 0.23/0.52          | ~ (m1_subset_1 @ X21 @ 
% 0.23/0.52               (k1_zfmisc_1 @ 
% 0.23/0.52                (u1_struct_0 @ 
% 0.23/0.52                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))))
% 0.23/0.52          | ((k7_subset_1 @ 
% 0.23/0.52              (u1_struct_0 @ 
% 0.23/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22)))) @ 
% 0.23/0.52              X21 @ (k1_tarski @ k1_xboole_0))
% 0.23/0.52              = (k2_yellow19 @ X22 @ 
% 0.23/0.52                 (k3_yellow19 @ X22 @ (k2_struct_0 @ X22) @ X21)))
% 0.23/0.52          | ~ (l1_struct_0 @ X22)
% 0.23/0.52          | (v2_struct_0 @ X22))),
% 0.23/0.52      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.23/0.52        | ((k7_subset_1 @ 
% 0.23/0.52            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.23/0.52            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.23/0.52            = (k2_yellow19 @ sk_A @ 
% 0.23/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.23/0.52        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.23/0.52             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.23/0.52        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.23/0.52             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.23/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '27'])).
% 0.23/0.52  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (k1_zfmisc_1 @ 
% 0.23/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.23/0.52          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k7_subset_1 @ 
% 0.23/0.52           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.23/0.52           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      ((v13_waybel_0 @ sk_B_1 @ 
% 0.23/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      ((v2_waybel_0 @ sk_B_1 @ 
% 0.23/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.23/0.52  thf('39', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.23/0.52            = (k2_yellow19 @ sk_A @ 
% 0.23/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.23/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.52      inference('demod', [status(thm)], ['28', '29', '32', '35', '38'])).
% 0.23/0.52  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('41', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_B_1)
% 0.23/0.52        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.23/0.52            = (k2_yellow19 @ sk_A @ 
% 0.23/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.23/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.23/0.52  thf('42', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.23/0.52         = (k2_yellow19 @ sk_A @ 
% 0.23/0.52            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.23/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.23/0.52  thf('44', plain,
% 0.23/0.52      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.23/0.52      inference('demod', [status(thm)], ['18', '43'])).
% 0.23/0.52  thf('45', plain,
% 0.23/0.52      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '44'])).
% 0.23/0.52  thf('46', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.23/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.23/0.52  thf('47', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (k1_zfmisc_1 @ 
% 0.23/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf(t2_yellow19, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.23/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.23/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.23/0.52             ( m1_subset_1 @
% 0.23/0.52               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.23/0.52           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.23/0.52  thf('48', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X23)
% 0.23/0.52          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.23/0.52          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X24))
% 0.23/0.52          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X24))
% 0.23/0.52          | ~ (m1_subset_1 @ X23 @ 
% 0.23/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))
% 0.23/0.52          | ~ (r2_hidden @ X25 @ X23)
% 0.23/0.52          | ~ (v1_xboole_0 @ X25)
% 0.23/0.52          | (v1_xboole_0 @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.23/0.52  thf('49', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('52', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('53', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X23)
% 0.23/0.52          | ~ (v1_subset_1 @ X23 @ 
% 0.23/0.52               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24))))
% 0.23/0.52          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.23/0.52          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.23/0.52          | ~ (m1_subset_1 @ X23 @ 
% 0.23/0.52               (k1_zfmisc_1 @ 
% 0.23/0.52                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 0.23/0.52          | ~ (r2_hidden @ X25 @ X23)
% 0.23/0.52          | ~ (v1_xboole_0 @ X25)
% 0.23/0.52          | (v1_xboole_0 @ X24))),
% 0.23/0.52      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.23/0.52  thf('54', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.23/0.52          | ~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.23/0.52          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.23/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.23/0.52          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.23/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.23/0.52          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.23/0.52               (u1_struct_0 @ 
% 0.23/0.52                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.23/0.52          | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['47', '53'])).
% 0.23/0.52  thf('55', plain,
% 0.23/0.52      ((v13_waybel_0 @ sk_B_1 @ 
% 0.23/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.23/0.52  thf('56', plain,
% 0.23/0.52      ((v2_waybel_0 @ sk_B_1 @ 
% 0.23/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.23/0.52  thf('57', plain,
% 0.23/0.52      ((v1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('58', plain,
% 0.23/0.52      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.23/0.52  thf('59', plain,
% 0.23/0.52      ((v1_subset_1 @ sk_B_1 @ 
% 0.23/0.52        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.23/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('60', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.23/0.52          | ~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.23/0.52          | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.52      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 0.23/0.52  thf('61', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_B_1)
% 0.23/0.52        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['46', '60'])).
% 0.23/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.52  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.52  thf('63', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.23/0.52  thf('64', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('65', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.23/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.23/0.52  thf(fc5_struct_0, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.52       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.23/0.52  thf('66', plain,
% 0.23/0.52      (![X19 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ (k2_struct_0 @ X19))
% 0.23/0.52          | ~ (l1_struct_0 @ X19)
% 0.23/0.52          | (v2_struct_0 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.23/0.52  thf('67', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.52  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.23/0.52  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
