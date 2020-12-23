%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGlHrvSzQ9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 230 expanded)
%              Number of leaves         :   43 (  91 expanded)
%              Depth                    :   17
%              Number of atoms          : 1161 (2897 expanded)
%              Number of equality atoms :   53 ( 117 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) )
      | ( X14 = X15 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) @ X23 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) @ X23 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41','44','47','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','55'])).

thf('57',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','56'])).

thf('58',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

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

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_yellow_1 @ X26 ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_yellow_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('71',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('75',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('80',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','77','82','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('94',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','99'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGlHrvSzQ9
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:46:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 162 iterations in 0.073s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.19/0.48  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.19/0.48  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.19/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.19/0.48  thf(t15_yellow19, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48             ( v1_subset_1 @
% 0.19/0.48               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( m1_subset_1 @
% 0.19/0.48               B @ 
% 0.19/0.48               ( k1_zfmisc_1 @
% 0.19/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.48           ( ( B ) =
% 0.19/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48                ( v1_subset_1 @
% 0.19/0.48                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.48                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48                ( m1_subset_1 @
% 0.19/0.48                  B @ 
% 0.19/0.48                  ( k1_zfmisc_1 @
% 0.19/0.48                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.48              ( ( B ) =
% 0.19/0.48                ( k2_yellow19 @
% 0.19/0.48                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.19/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf(t17_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) != ( B ) ) =>
% 0.19/0.48       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15))
% 0.19/0.48          | ((X14) = (X15)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.19/0.48  thf(l24_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X12) @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.48          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ X1)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.19/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '14'])).
% 0.19/0.48  thf(t1_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X19 : $i]:
% 0.19/0.48         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.19/0.48  thf(t4_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.19/0.48          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ X1)
% 0.19/0.48          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.48  thf(t100_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X8 @ X9)
% 0.19/0.48           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.19/0.48            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.48  thf('22', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X8 @ X9)
% 0.19/0.48           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf(t3_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('27', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.48  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.19/0.48          | (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (((sk_B_1)
% 0.19/0.48         != (k2_yellow19 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d2_yellow_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf(t14_yellow19, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( m1_subset_1 @
% 0.19/0.48               B @ 
% 0.19/0.48               ( k1_zfmisc_1 @
% 0.19/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.48           ( ( k7_subset_1 @
% 0.19/0.48               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.19/0.48               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.19/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X23)
% 0.19/0.48          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))))
% 0.19/0.48          | ((k7_subset_1 @ 
% 0.19/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24))) @ X23 @ 
% 0.19/0.48              (k1_tarski @ k1_xboole_0))
% 0.19/0.48              = (k2_yellow19 @ X24 @ 
% 0.19/0.48                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.19/0.48          | ~ (l1_struct_0 @ X24)
% 0.19/0.48          | (v2_struct_0 @ X24))),
% 0.19/0.48      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X23)
% 0.19/0.48          | ~ (v2_waybel_0 @ X23 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.19/0.48          | ~ (v13_waybel_0 @ X23 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ 
% 0.19/0.48                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))))
% 0.19/0.48          | ((k7_subset_1 @ 
% 0.19/0.48              (u1_struct_0 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24)))) @ 
% 0.19/0.48              X23 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.48              = (k2_yellow19 @ X24 @ 
% 0.19/0.48                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.19/0.48          | ~ (l1_struct_0 @ X24)
% 0.19/0.48          | (v2_struct_0 @ X24))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | ((k7_subset_1 @ 
% 0.19/0.48            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.19/0.48            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.19/0.48        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '39'])).
% 0.19/0.48  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.48          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k7_subset_1 @ 
% 0.19/0.48           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.19/0.48           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['40', '41', '44', '47', '50'])).
% 0.19/0.48  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.48        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.19/0.48      inference('clc', [status(thm)], ['51', '52'])).
% 0.19/0.48  thf('54', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.48         = (k2_yellow19 @ sk_A @ 
% 0.19/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '55'])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '56'])).
% 0.19/0.48  thf('58', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['57'])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.19/0.48          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf(d3_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      (![X20 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      (((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48         (k1_zfmisc_1 @ 
% 0.19/0.48          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.48  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['63', '64'])).
% 0.19/0.48  thf(t2_yellow19, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.19/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.19/0.48             ( m1_subset_1 @
% 0.19/0.48               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.19/0.48           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X25)
% 0.19/0.48          | ~ (v1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X26)))
% 0.19/0.48          | ~ (v2_waybel_0 @ X25 @ (k3_yellow_1 @ X26))
% 0.19/0.48          | ~ (v13_waybel_0 @ X25 @ (k3_yellow_1 @ X26))
% 0.19/0.48          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X26))))
% 0.19/0.48          | ~ (r2_hidden @ X27 @ X25)
% 0.19/0.48          | ~ (v1_xboole_0 @ X27)
% 0.19/0.48          | (v1_xboole_0 @ X26))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.19/0.48  thf('67', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('70', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('71', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X25)
% 0.19/0.48          | ~ (v1_subset_1 @ X25 @ 
% 0.19/0.48               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X26))))
% 0.19/0.48          | ~ (v2_waybel_0 @ X25 @ (k3_lattice3 @ (k1_lattice3 @ X26)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X25 @ (k3_lattice3 @ (k1_lattice3 @ X26)))
% 0.19/0.48          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X26)))))
% 0.19/0.48          | ~ (r2_hidden @ X27 @ X25)
% 0.19/0.48          | ~ (v1_xboole_0 @ X27)
% 0.19/0.48          | (v1_xboole_0 @ X26))),
% 0.19/0.48      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | ~ (v1_xboole_0 @ X0)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.48          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.19/0.48               (u1_struct_0 @ 
% 0.19/0.48                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['65', '71'])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      (![X20 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('75', plain,
% 0.19/0.48      (((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['73', '74'])).
% 0.19/0.48  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('77', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.48  thf('78', plain,
% 0.19/0.48      (![X20 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf('79', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.48  thf('80', plain,
% 0.19/0.48      (((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['78', '79'])).
% 0.19/0.48  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B_1 @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.48  thf('83', plain,
% 0.19/0.48      (![X20 : $i]:
% 0.19/0.48         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.48  thf('84', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('85', plain,
% 0.19/0.48      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('86', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('demod', [status(thm)], ['84', '85'])).
% 0.19/0.48  thf('87', plain,
% 0.19/0.48      (((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['83', '86'])).
% 0.19/0.48  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('89', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B_1 @ 
% 0.19/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.48  thf('90', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | ~ (v1_xboole_0 @ X0)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['72', '77', '82', '89'])).
% 0.19/0.48  thf('91', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['60', '90'])).
% 0.19/0.48  thf('92', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['59', '91'])).
% 0.19/0.48  thf('93', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['92'])).
% 0.19/0.48  thf(fc2_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('94', plain,
% 0.19/0.48      (![X21 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.19/0.48          | ~ (l1_struct_0 @ X21)
% 0.19/0.48          | (v2_struct_0 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.48  thf('95', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['93', '94'])).
% 0.19/0.48  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('97', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0)
% 0.19/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['95', '96'])).
% 0.19/0.48  thf('98', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X12) @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.48  thf('99', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48          | ~ (v1_xboole_0 @ X0)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['97', '98'])).
% 0.19/0.48  thf('100', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['58', '99'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('102', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['100', '101'])).
% 0.19/0.48  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['102', '103'])).
% 0.19/0.48  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
