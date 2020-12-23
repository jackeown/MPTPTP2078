%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6IILsEystQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 302 expanded)
%              Number of leaves         :   47 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          : 1310 (3126 expanded)
%              Number of equality atoms :   82 ( 196 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X21 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( sk_B @ ( k4_xboole_0 @ X0 @ X1 ) )
        = X2 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) )
        = X0 )
      | ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_B @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['24','53'])).

thf('55',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('57',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('60',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('63',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('64',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('66',plain,(
    ! [X25: $i] :
      ( ( k9_setfam_1 @ X25 )
      = ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('67',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X31 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X31 ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','65','66','67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X25: $i] :
      ( ( k9_setfam_1 @ X25 )
      = ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('78',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('79',plain,(
    ! [X25: $i] :
      ( ( k9_setfam_1 @ X25 )
      = ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('83',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['70','71','81','82','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','90'])).

thf('92',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','91'])).

thf('93',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('95',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('96',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('97',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('98',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('100',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('101',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('102',plain,(
    ! [X25: $i] :
      ( ( k9_setfam_1 @ X25 )
      = ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('103',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X33 ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('106',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('107',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X28: $i] :
      ( ( k3_yellow_1 @ X28 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('109',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      = ( k9_setfam_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('111',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','112'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('121',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['0','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6IILsEystQ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.83/3.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.83/3.08  % Solved by: fo/fo7.sh
% 2.83/3.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.83/3.08  % done 6405 iterations in 2.615s
% 2.83/3.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.83/3.08  % SZS output start Refutation
% 2.83/3.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.83/3.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.83/3.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.83/3.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.83/3.08  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 2.83/3.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.83/3.08  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 2.83/3.08  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.83/3.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 2.83/3.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.83/3.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.83/3.08  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 2.83/3.08  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 2.83/3.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(sk_B_type, type, sk_B: $i > $i).
% 2.83/3.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.83/3.08  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 2.83/3.08  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 2.83/3.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.83/3.08  thf(sk_A_type, type, sk_A: $i).
% 2.83/3.08  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 2.83/3.08  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.83/3.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.83/3.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.83/3.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.83/3.08  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 2.83/3.08  thf(t15_yellow19, conjecture,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.83/3.08       ( ![B:$i]:
% 2.83/3.08         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.83/3.08             ( v1_subset_1 @
% 2.83/3.08               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 2.83/3.08             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.08             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.08             ( m1_subset_1 @
% 2.83/3.08               B @ 
% 2.83/3.08               ( k1_zfmisc_1 @
% 2.83/3.08                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.83/3.08           ( ( B ) =
% 2.83/3.08             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.83/3.08  thf(zf_stmt_0, negated_conjecture,
% 2.83/3.08    (~( ![A:$i]:
% 2.83/3.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.83/3.08          ( ![B:$i]:
% 2.83/3.08            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.83/3.08                ( v1_subset_1 @
% 2.83/3.08                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 2.83/3.08                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.08                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.08                ( m1_subset_1 @
% 2.83/3.08                  B @ 
% 2.83/3.08                  ( k1_zfmisc_1 @
% 2.83/3.08                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.83/3.08              ( ( B ) =
% 2.83/3.08                ( k2_yellow19 @
% 2.83/3.08                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 2.83/3.08    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 2.83/3.08  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf(d3_struct_0, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.83/3.08  thf('1', plain,
% 2.83/3.08      (![X26 : $i]:
% 2.83/3.08         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 2.83/3.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.83/3.08  thf(d1_xboole_0, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.83/3.08  thf('2', plain,
% 2.83/3.08      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.83/3.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.83/3.08  thf(d5_xboole_0, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.83/3.08       ( ![D:$i]:
% 2.83/3.08         ( ( r2_hidden @ D @ C ) <=>
% 2.83/3.08           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.83/3.08  thf('3', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X7 @ X6)
% 2.83/3.08          | (r2_hidden @ X7 @ X4)
% 2.83/3.08          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.83/3.08  thf('4', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.83/3.08         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['3'])).
% 2.83/3.08  thf('5', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.83/3.08          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['2', '4'])).
% 2.83/3.08  thf(t64_zfmisc_1, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.83/3.08       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.83/3.08  thf('6', plain,
% 2.83/3.08      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.83/3.08         ((r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X21)))
% 2.83/3.08          | ((X18) = (X21))
% 2.83/3.08          | ~ (r2_hidden @ X18 @ X19))),
% 2.83/3.08      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 2.83/3.08  thf('7', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 2.83/3.08          | ((sk_B @ (k4_xboole_0 @ X0 @ X1)) = (X2))
% 2.83/3.08          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X0 @ X1)) @ 
% 2.83/3.08             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['5', '6'])).
% 2.83/3.08  thf('8', plain,
% 2.83/3.08      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.83/3.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.83/3.08  thf('9', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X7 @ X6)
% 2.83/3.08          | ~ (r2_hidden @ X7 @ X5)
% 2.83/3.08          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.83/3.08  thf('10', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X7 @ X5)
% 2.83/3.08          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['9'])).
% 2.83/3.08  thf('11', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.83/3.08          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['8', '10'])).
% 2.83/3.08  thf('12', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (((sk_B @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))
% 2.83/3.08            = (X0))
% 2.83/3.08          | (v1_xboole_0 @ 
% 2.83/3.08             (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))
% 2.83/3.08          | (v1_xboole_0 @ 
% 2.83/3.08             (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['7', '11'])).
% 2.83/3.08  thf(t48_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.83/3.08  thf('13', plain,
% 2.83/3.08      (![X12 : $i, X13 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.83/3.08           = (k3_xboole_0 @ X12 @ X13))),
% 2.83/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.83/3.08  thf('14', plain,
% 2.83/3.08      (![X12 : $i, X13 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.83/3.08           = (k3_xboole_0 @ X12 @ X13))),
% 2.83/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.83/3.08  thf('15', plain,
% 2.83/3.08      (![X12 : $i, X13 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.83/3.08           = (k3_xboole_0 @ X12 @ X13))),
% 2.83/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.83/3.08  thf('16', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (((sk_B @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))) = (X0))
% 2.83/3.08          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.83/3.08          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.83/3.08      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 2.83/3.08  thf('17', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.83/3.08          | ((sk_B @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['16'])).
% 2.83/3.08  thf('18', plain,
% 2.83/3.08      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.83/3.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.83/3.08  thf('19', plain,
% 2.83/3.08      (![X12 : $i, X13 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.83/3.08           = (k3_xboole_0 @ X12 @ X13))),
% 2.83/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.83/3.08  thf('20', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.83/3.08         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['3'])).
% 2.83/3.08  thf('21', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['19', '20'])).
% 2.83/3.08  thf('22', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 2.83/3.08          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['18', '21'])).
% 2.83/3.08  thf('23', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r2_hidden @ X0 @ X1)
% 2.83/3.08          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.83/3.08          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.83/3.08      inference('sup+', [status(thm)], ['17', '22'])).
% 2.83/3.08  thf('24', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.83/3.08          | (r2_hidden @ X0 @ X1))),
% 2.83/3.08      inference('simplify', [status(thm)], ['23'])).
% 2.83/3.08  thf('25', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.83/3.08         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 2.83/3.08          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 2.83/3.08          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 2.83/3.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.83/3.08  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.83/3.08  thf('26', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 2.83/3.08      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.83/3.08  thf(l24_zfmisc_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 2.83/3.08  thf('27', plain,
% 2.83/3.08      (![X16 : $i, X17 : $i]:
% 2.83/3.08         (~ (r1_xboole_0 @ (k1_tarski @ X16) @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 2.83/3.08      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 2.83/3.08  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.83/3.08      inference('sup-', [status(thm)], ['26', '27'])).
% 2.83/3.08  thf('29', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.83/3.08          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['25', '28'])).
% 2.83/3.08  thf(t4_boole, axiom,
% 2.83/3.08    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.83/3.08  thf('30', plain,
% 2.83/3.08      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 2.83/3.08      inference('cnf', [status(esa)], [t4_boole])).
% 2.83/3.08  thf('31', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.83/3.08          | ((X1) = (k1_xboole_0)))),
% 2.83/3.08      inference('demod', [status(thm)], ['29', '30'])).
% 2.83/3.08  thf('32', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.83/3.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.83/3.08  thf('33', plain,
% 2.83/3.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['31', '32'])).
% 2.83/3.08  thf(t100_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.83/3.08  thf('34', plain,
% 2.83/3.08      (![X9 : $i, X10 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X9 @ X10)
% 2.83/3.08           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.83/3.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.83/3.08  thf(t3_boole, axiom,
% 2.83/3.08    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.83/3.08  thf('35', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 2.83/3.08      inference('cnf', [status(esa)], [t3_boole])).
% 2.83/3.08  thf('36', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['34', '35'])).
% 2.83/3.08  thf('37', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.83/3.08          | ((X1) = (k1_xboole_0)))),
% 2.83/3.08      inference('demod', [status(thm)], ['29', '30'])).
% 2.83/3.08  thf('38', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 2.83/3.08      inference('cnf', [status(esa)], [t3_boole])).
% 2.83/3.08  thf('39', plain,
% 2.83/3.08      (![X12 : $i, X13 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 2.83/3.08           = (k3_xboole_0 @ X12 @ X13))),
% 2.83/3.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.83/3.08  thf('40', plain,
% 2.83/3.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['38', '39'])).
% 2.83/3.08  thf('41', plain,
% 2.83/3.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['38', '39'])).
% 2.83/3.08  thf('42', plain,
% 2.83/3.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['38', '39'])).
% 2.83/3.08  thf('43', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X7 @ X5)
% 2.83/3.08          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['9'])).
% 2.83/3.08  thf('44', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 2.83/3.08          | ~ (r2_hidden @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('45', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 2.83/3.08          | ~ (r2_hidden @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['41', '44'])).
% 2.83/3.08  thf('46', plain,
% 2.83/3.08      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.83/3.08         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 2.83/3.08      inference('simplify', [status(thm)], ['3'])).
% 2.83/3.08  thf('47', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.83/3.08      inference('clc', [status(thm)], ['45', '46'])).
% 2.83/3.08  thf('48', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['40', '47'])).
% 2.83/3.08  thf('49', plain,
% 2.83/3.08      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['37', '48'])).
% 2.83/3.08  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.83/3.08      inference('demod', [status(thm)], ['36', '49'])).
% 2.83/3.08  thf('51', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['33', '50'])).
% 2.83/3.08  thf('52', plain,
% 2.83/3.08      (![X9 : $i, X10 : $i]:
% 2.83/3.08         ((k4_xboole_0 @ X9 @ X10)
% 2.83/3.08           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.83/3.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.83/3.08  thf('53', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 2.83/3.09          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.83/3.09      inference('sup+', [status(thm)], ['51', '52'])).
% 2.83/3.09  thf('54', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         ((r2_hidden @ X0 @ X1)
% 2.83/3.09          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['24', '53'])).
% 2.83/3.09  thf('55', plain,
% 2.83/3.09      (((sk_B_1)
% 2.83/3.09         != (k2_yellow19 @ sk_A @ 
% 2.83/3.09             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('56', plain,
% 2.83/3.09      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf(d2_yellow_1, axiom,
% 2.83/3.09    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 2.83/3.09  thf('57', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('58', plain,
% 2.83/3.09      ((v2_waybel_0 @ sk_B_1 @ 
% 2.83/3.09        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['56', '57'])).
% 2.83/3.09  thf(t14_yellow19, axiom,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.83/3.09       ( ![B:$i]:
% 2.83/3.09         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.83/3.09             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.09             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 2.83/3.09             ( m1_subset_1 @
% 2.83/3.09               B @ 
% 2.83/3.09               ( k1_zfmisc_1 @
% 2.83/3.09                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 2.83/3.09           ( ( k7_subset_1 @
% 2.83/3.09               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 2.83/3.09               ( k1_tarski @ k1_xboole_0 ) ) =
% 2.83/3.09             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.83/3.09  thf('59', plain,
% 2.83/3.09      (![X30 : $i, X31 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ X30)
% 2.83/3.09          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 2.83/3.09          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 2.83/3.09          | ~ (m1_subset_1 @ X30 @ 
% 2.83/3.09               (k1_zfmisc_1 @ 
% 2.83/3.09                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))))
% 2.83/3.09          | ((k7_subset_1 @ 
% 2.83/3.09              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31))) @ X30 @ 
% 2.83/3.09              (k1_tarski @ k1_xboole_0))
% 2.83/3.09              = (k2_yellow19 @ X31 @ 
% 2.83/3.09                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 2.83/3.09          | ~ (l1_struct_0 @ X31)
% 2.83/3.09          | (v2_struct_0 @ X31))),
% 2.83/3.09      inference('cnf', [status(esa)], [t14_yellow19])).
% 2.83/3.09  thf('60', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('61', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('62', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf(t4_waybel_7, axiom,
% 2.83/3.09    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 2.83/3.09  thf('63', plain,
% 2.83/3.09      (![X29 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X29)) = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('cnf', [status(esa)], [t4_waybel_7])).
% 2.83/3.09  thf('64', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('65', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf(redefinition_k9_setfam_1, axiom,
% 2.83/3.09    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 2.83/3.09  thf('66', plain, (![X25 : $i]: ((k9_setfam_1 @ X25) = (k1_zfmisc_1 @ X25))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 2.83/3.09  thf('67', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('68', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf('69', plain,
% 2.83/3.09      (![X30 : $i, X31 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ X30)
% 2.83/3.09          | ~ (v2_waybel_0 @ X30 @ 
% 2.83/3.09               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 2.83/3.09          | ~ (v13_waybel_0 @ X30 @ 
% 2.83/3.09               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 2.83/3.09          | ~ (m1_subset_1 @ X30 @ 
% 2.83/3.09               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X31))))
% 2.83/3.09          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X31)) @ X30 @ 
% 2.83/3.09              (k1_tarski @ k1_xboole_0))
% 2.83/3.09              = (k2_yellow19 @ X31 @ 
% 2.83/3.09                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 2.83/3.09          | ~ (l1_struct_0 @ X31)
% 2.83/3.09          | (v2_struct_0 @ X31))),
% 2.83/3.09      inference('demod', [status(thm)],
% 2.83/3.09                ['59', '60', '61', '62', '65', '66', '67', '68'])).
% 2.83/3.09  thf('70', plain,
% 2.83/3.09      (((v2_struct_0 @ sk_A)
% 2.83/3.09        | ~ (l1_struct_0 @ sk_A)
% 2.83/3.09        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ 
% 2.83/3.09            (k1_tarski @ k1_xboole_0))
% 2.83/3.09            = (k2_yellow19 @ sk_A @ 
% 2.83/3.09               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.83/3.09        | ~ (m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09             (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 2.83/3.09        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 2.83/3.09             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.83/3.09        | (v1_xboole_0 @ sk_B_1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['58', '69'])).
% 2.83/3.09  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('72', plain,
% 2.83/3.09      ((m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('73', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('74', plain, (![X25 : $i]: ((k9_setfam_1 @ X25) = (k1_zfmisc_1 @ X25))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 2.83/3.09  thf('75', plain,
% 2.83/3.09      ((m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (k9_setfam_1 @ 
% 2.83/3.09         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 2.83/3.09      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.83/3.09  thf('76', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf('77', plain,
% 2.83/3.09      ((m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['75', '76'])).
% 2.83/3.09  thf(redefinition_k7_subset_1, axiom,
% 2.83/3.09    (![A:$i,B:$i,C:$i]:
% 2.83/3.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.83/3.09       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.83/3.09  thf('78', plain,
% 2.83/3.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.09         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.83/3.09          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.83/3.09  thf('79', plain, (![X25 : $i]: ((k9_setfam_1 @ X25) = (k1_zfmisc_1 @ X25))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 2.83/3.09  thf('80', plain,
% 2.83/3.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.09         (~ (m1_subset_1 @ X22 @ (k9_setfam_1 @ X23))
% 2.83/3.09          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 2.83/3.09      inference('demod', [status(thm)], ['78', '79'])).
% 2.83/3.09  thf('81', plain,
% 2.83/3.09      (![X0 : $i]:
% 2.83/3.09         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ X0)
% 2.83/3.09           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 2.83/3.09      inference('sup-', [status(thm)], ['77', '80'])).
% 2.83/3.09  thf('82', plain,
% 2.83/3.09      ((m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['75', '76'])).
% 2.83/3.09  thf('83', plain,
% 2.83/3.09      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('84', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('85', plain,
% 2.83/3.09      ((v13_waybel_0 @ sk_B_1 @ 
% 2.83/3.09        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['83', '84'])).
% 2.83/3.09  thf('86', plain,
% 2.83/3.09      (((v2_struct_0 @ sk_A)
% 2.83/3.09        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.83/3.09            = (k2_yellow19 @ sk_A @ 
% 2.83/3.09               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.83/3.09        | (v1_xboole_0 @ sk_B_1))),
% 2.83/3.09      inference('demod', [status(thm)], ['70', '71', '81', '82', '85'])).
% 2.83/3.09  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('88', plain,
% 2.83/3.09      (((v1_xboole_0 @ sk_B_1)
% 2.83/3.09        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.83/3.09            = (k2_yellow19 @ sk_A @ 
% 2.83/3.09               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 2.83/3.09      inference('clc', [status(thm)], ['86', '87'])).
% 2.83/3.09  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('90', plain,
% 2.83/3.09      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 2.83/3.09         = (k2_yellow19 @ sk_A @ 
% 2.83/3.09            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.83/3.09      inference('clc', [status(thm)], ['88', '89'])).
% 2.83/3.09  thf('91', plain,
% 2.83/3.09      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 2.83/3.09      inference('demod', [status(thm)], ['55', '90'])).
% 2.83/3.09  thf('92', plain,
% 2.83/3.09      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['54', '91'])).
% 2.83/3.09  thf('93', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 2.83/3.09      inference('simplify', [status(thm)], ['92'])).
% 2.83/3.09  thf('94', plain,
% 2.83/3.09      ((v2_waybel_0 @ sk_B_1 @ 
% 2.83/3.09        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['56', '57'])).
% 2.83/3.09  thf(t2_yellow19, axiom,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.83/3.09       ( ![B:$i]:
% 2.83/3.09         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.83/3.09             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 2.83/3.09             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 2.83/3.09             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 2.83/3.09             ( m1_subset_1 @
% 2.83/3.09               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 2.83/3.09           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 2.83/3.09  thf('95', plain,
% 2.83/3.09      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ X32)
% 2.83/3.09          | ~ (v1_subset_1 @ X32 @ (u1_struct_0 @ (k3_yellow_1 @ X33)))
% 2.83/3.09          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 2.83/3.09          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 2.83/3.09          | ~ (m1_subset_1 @ X32 @ 
% 2.83/3.09               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X33))))
% 2.83/3.09          | ~ (r2_hidden @ X34 @ X32)
% 2.83/3.09          | ~ (v1_xboole_0 @ X34)
% 2.83/3.09          | (v1_xboole_0 @ X33))),
% 2.83/3.09      inference('cnf', [status(esa)], [t2_yellow19])).
% 2.83/3.09  thf('96', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('97', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf('98', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('99', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('100', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('101', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf('102', plain, (![X25 : $i]: ((k9_setfam_1 @ X25) = (k1_zfmisc_1 @ X25))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 2.83/3.09  thf('103', plain,
% 2.83/3.09      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ X32)
% 2.83/3.09          | ~ (v1_subset_1 @ X32 @ (k9_setfam_1 @ X33))
% 2.83/3.09          | ~ (v2_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 2.83/3.09          | ~ (v13_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 2.83/3.09          | ~ (m1_subset_1 @ X32 @ (k9_setfam_1 @ (k9_setfam_1 @ X33)))
% 2.83/3.09          | ~ (r2_hidden @ X34 @ X32)
% 2.83/3.09          | ~ (v1_xboole_0 @ X34)
% 2.83/3.09          | (v1_xboole_0 @ X33))),
% 2.83/3.09      inference('demod', [status(thm)],
% 2.83/3.09                ['95', '96', '97', '98', '99', '100', '101', '102'])).
% 2.83/3.09  thf('104', plain,
% 2.83/3.09      (![X0 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.83/3.09          | ~ (v1_xboole_0 @ X0)
% 2.83/3.09          | ~ (r2_hidden @ X0 @ sk_B_1)
% 2.83/3.09          | ~ (m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 2.83/3.09          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 2.83/3.09               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 2.83/3.09          | ~ (v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))
% 2.83/3.09          | (v1_xboole_0 @ sk_B_1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['94', '103'])).
% 2.83/3.09  thf('105', plain,
% 2.83/3.09      ((m1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['75', '76'])).
% 2.83/3.09  thf('106', plain,
% 2.83/3.09      ((v13_waybel_0 @ sk_B_1 @ 
% 2.83/3.09        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('demod', [status(thm)], ['83', '84'])).
% 2.83/3.09  thf('107', plain,
% 2.83/3.09      ((v1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('108', plain,
% 2.83/3.09      (![X28 : $i]: ((k3_yellow_1 @ X28) = (k3_lattice3 @ (k1_lattice3 @ X28)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d2_yellow_1])).
% 2.83/3.09  thf('109', plain,
% 2.83/3.09      ((v1_subset_1 @ sk_B_1 @ 
% 2.83/3.09        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 2.83/3.09      inference('demod', [status(thm)], ['107', '108'])).
% 2.83/3.09  thf('110', plain,
% 2.83/3.09      (![X29 : $i]:
% 2.83/3.09         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 2.83/3.09           = (k9_setfam_1 @ X29))),
% 2.83/3.09      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.09  thf('111', plain,
% 2.83/3.09      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 2.83/3.09      inference('demod', [status(thm)], ['109', '110'])).
% 2.83/3.09  thf('112', plain,
% 2.83/3.09      (![X0 : $i]:
% 2.83/3.09         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.83/3.09          | ~ (v1_xboole_0 @ X0)
% 2.83/3.09          | ~ (r2_hidden @ X0 @ sk_B_1)
% 2.83/3.09          | (v1_xboole_0 @ sk_B_1))),
% 2.83/3.09      inference('demod', [status(thm)], ['104', '105', '106', '111'])).
% 2.83/3.09  thf('113', plain,
% 2.83/3.09      (((v1_xboole_0 @ sk_B_1)
% 2.83/3.09        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.83/3.09        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['93', '112'])).
% 2.83/3.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.83/3.09  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.83/3.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.83/3.09  thf('115', plain,
% 2.83/3.09      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.83/3.09      inference('demod', [status(thm)], ['113', '114'])).
% 2.83/3.09  thf('116', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('117', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 2.83/3.09      inference('clc', [status(thm)], ['115', '116'])).
% 2.83/3.09  thf('118', plain,
% 2.83/3.09      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.83/3.09      inference('sup+', [status(thm)], ['1', '117'])).
% 2.83/3.09  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('120', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 2.83/3.09      inference('demod', [status(thm)], ['118', '119'])).
% 2.83/3.09  thf(fc2_struct_0, axiom,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.83/3.09       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.83/3.09  thf('121', plain,
% 2.83/3.09      (![X27 : $i]:
% 2.83/3.09         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 2.83/3.09          | ~ (l1_struct_0 @ X27)
% 2.83/3.09          | (v2_struct_0 @ X27))),
% 2.83/3.09      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.83/3.09  thf('122', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 2.83/3.09      inference('sup-', [status(thm)], ['120', '121'])).
% 2.83/3.09  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.09  thf('124', plain, ((v2_struct_0 @ sk_A)),
% 2.83/3.09      inference('demod', [status(thm)], ['122', '123'])).
% 2.83/3.09  thf('125', plain, ($false), inference('demod', [status(thm)], ['0', '124'])).
% 2.83/3.09  
% 2.83/3.09  % SZS output end Refutation
% 2.83/3.09  
% 2.83/3.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
