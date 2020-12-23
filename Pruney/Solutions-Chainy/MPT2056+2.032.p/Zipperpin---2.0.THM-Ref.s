%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wIA0keiFsE

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 263 expanded)
%              Number of leaves         :   44 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          : 1222 (3106 expanded)
%              Number of equality atoms :   58 ( 127 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','39'])).

thf('41',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('43',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

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

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X28 ) ) ) @ X27 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X28 @ ( k3_yellow19 @ X28 @ ( k2_struct_0 @ X28 ) @ X27 ) ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X28 ) ) ) ) @ X27 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X28 @ ( k3_yellow19 @ X28 @ ( k2_struct_0 @ X28 ) @ X27 ) ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['51','52','55','58','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','66'])).

thf('68',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','67'])).

thf('69',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_yellow_1 @ X30 ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_yellow_1 @ X30 ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_yellow_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X30 ) ) ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('80',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('88',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('93',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['85','90','95','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_2 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['72','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('107',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wIA0keiFsE
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 266 iterations in 0.102s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.55  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(t15_yellow19, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55             ( v1_subset_1 @
% 0.21/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( m1_subset_1 @
% 0.21/0.55               B @ 
% 0.21/0.55               ( k1_zfmisc_1 @
% 0.21/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.55           ( ( B ) =
% 0.21/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55                ( v1_subset_1 @
% 0.21/0.55                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.55                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55                ( m1_subset_1 @
% 0.21/0.55                  B @ 
% 0.21/0.55                  ( k1_zfmisc_1 @
% 0.21/0.55                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.55              ( ( B ) =
% 0.21/0.55                ( k2_yellow19 @
% 0.21/0.55                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf(t17_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) != ( B ) ) =>
% 0.21/0.55       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.21/0.55          | ((X16) = (X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.55  thf(l24_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X14) @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.21/0.55          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.21/0.55          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf(t1_mcart_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X23) @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.21/0.55  thf(t4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.21/0.55          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ X1)
% 0.21/0.55          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X11 @ X12)
% 0.21/0.55           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.21/0.55            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.55  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf(d1_xboole_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.21/0.56          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X7 @ X8)
% 0.21/0.56          | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ k1_xboole_0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.56  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '31'])).
% 0.21/0.56  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X11 @ X12)
% 0.21/0.56           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf(t3_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.56  thf('38', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.56  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.21/0.56          | (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('demod', [status(thm)], ['14', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (((sk_B_2)
% 0.21/0.56         != (k2_yellow19 @ sk_A @ 
% 0.21/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d2_yellow_1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf(t14_yellow19, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56             ( m1_subset_1 @
% 0.21/0.56               B @ 
% 0.21/0.56               ( k1_zfmisc_1 @
% 0.21/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.56           ( ( k7_subset_1 @
% 0.21/0.56               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.56               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X27)
% 0.21/0.56          | ~ (v2_waybel_0 @ X27 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))
% 0.21/0.56          | ~ (v13_waybel_0 @ X27 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X28)))))
% 0.21/0.56          | ((k7_subset_1 @ 
% 0.21/0.56              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X28))) @ X27 @ 
% 0.21/0.56              (k1_tarski @ k1_xboole_0))
% 0.21/0.56              = (k2_yellow19 @ X28 @ 
% 0.21/0.56                 (k3_yellow19 @ X28 @ (k2_struct_0 @ X28) @ X27)))
% 0.21/0.56          | ~ (l1_struct_0 @ X28)
% 0.21/0.56          | (v2_struct_0 @ X28))),
% 0.21/0.56      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X27)
% 0.21/0.56          | ~ (v2_waybel_0 @ X27 @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))
% 0.21/0.56          | ~ (v13_waybel_0 @ X27 @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ 
% 0.21/0.56                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28))))))
% 0.21/0.56          | ((k7_subset_1 @ 
% 0.21/0.56              (u1_struct_0 @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X28)))) @ 
% 0.21/0.56              X27 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.56              = (k2_yellow19 @ X28 @ 
% 0.21/0.56                 (k3_yellow19 @ X28 @ (k2_struct_0 @ X28) @ X27)))
% 0.21/0.56          | ~ (l1_struct_0 @ X28)
% 0.21/0.56          | (v2_struct_0 @ X28))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | ((k7_subset_1 @ 
% 0.21/0.56            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.56            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.56            = (k2_yellow19 @ sk_A @ 
% 0.21/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.56        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.56        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.56        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['44', '50'])).
% 0.21/0.56  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.21/0.56          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k7_subset_1 @ 
% 0.21/0.56           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.56           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.56            = (k2_yellow19 @ sk_A @ 
% 0.21/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.56        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '52', '55', '58', '61'])).
% 0.21/0.56  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.56        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.56            = (k2_yellow19 @ sk_A @ 
% 0.21/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.21/0.56      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('65', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.56         = (k2_yellow19 @ sk_A @ 
% 0.21/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.56      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['40', '67'])).
% 0.21/0.56  thf('69', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.21/0.56      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.21/0.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf(d3_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56         (k1_zfmisc_1 @ 
% 0.21/0.56          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf(t2_yellow19, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.56             ( m1_subset_1 @
% 0.21/0.56               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.56           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X29)
% 0.21/0.56          | ~ (v1_subset_1 @ X29 @ (u1_struct_0 @ (k3_yellow_1 @ X30)))
% 0.21/0.56          | ~ (v2_waybel_0 @ X29 @ (k3_yellow_1 @ X30))
% 0.21/0.56          | ~ (v13_waybel_0 @ X29 @ (k3_yellow_1 @ X30))
% 0.21/0.56          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X30))))
% 0.21/0.56          | ~ (r2_hidden @ X31 @ X29)
% 0.21/0.56          | ~ (v1_xboole_0 @ X31)
% 0.21/0.56          | (v1_xboole_0 @ X30))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X29)
% 0.21/0.56          | ~ (v1_subset_1 @ X29 @ 
% 0.21/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X30))))
% 0.21/0.56          | ~ (v2_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X30)))
% 0.21/0.56          | ~ (v13_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X30)))
% 0.21/0.56          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X30)))))
% 0.21/0.56          | ~ (r2_hidden @ X31 @ X29)
% 0.21/0.56          | ~ (v1_xboole_0 @ X31)
% 0.21/0.56          | (v1_xboole_0 @ X30))),
% 0.21/0.56      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.56          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.21/0.56               (u1_struct_0 @ 
% 0.21/0.56                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['78', '84'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      (((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.56  thf('91', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['91', '92'])).
% 0.21/0.56  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k3_lattice3 @ (k1_lattice3 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('99', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.56  thf('100', plain,
% 0.21/0.56      (((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['96', '99'])).
% 0.21/0.56  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['85', '90', '95', '102'])).
% 0.21/0.56  thf('104', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | ~ (v1_xboole_0 @ (sk_C @ sk_B_2 @ X0))
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['73', '103'])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0)
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['72', '104'])).
% 0.21/0.56  thf('106', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_2)
% 0.21/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['105'])).
% 0.21/0.56  thf(fc2_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.56  thf('107', plain,
% 0.21/0.56      (![X25 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.21/0.56          | ~ (l1_struct_0 @ X25)
% 0.21/0.56          | (v2_struct_0 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.56  thf('108', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0)
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.56  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('110', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0)
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_2)
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.56  thf('111', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ (k1_tarski @ X14) @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.56  thf('112', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.56  thf('113', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.56        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['69', '112'])).
% 0.21/0.56  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('115', plain, (((v1_xboole_0 @ sk_B_2) | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['113', '114'])).
% 0.21/0.56  thf('116', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('117', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('clc', [status(thm)], ['115', '116'])).
% 0.21/0.56  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
