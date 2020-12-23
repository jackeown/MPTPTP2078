%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4IJ5q2dVVS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 241 expanded)
%              Number of leaves         :   28 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          : 1007 (2467 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_wellord1_type,type,(
    r1_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t54_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ A @ B @ C ) )
               => ( v2_wellord1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( v2_wellord1 @ A )
                    & ( r3_wellord1 @ A @ B @ C ) )
                 => ( v2_wellord1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_wellord1])).

thf('0',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_wellord1 @ A )
      <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ~ ( v1_wellord1 @ X10 )
      | ( r1_wellord1 @ X10 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord1])).

thf(d14_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ( r6_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v6_relat_2 @ X1 )
      | ( r6_relat_2 @ X1 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_2])).

thf(d12_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf(d16_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ~ ( v8_relat_2 @ X2 )
      | ( r8_relat_2 @ X2 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf(d9_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ~ ( v1_relat_2 @ X6 )
      | ( r1_relat_2 @ X6 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf(d5_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_wellord1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B )
            & ( r1_wellord1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_relat_2 @ X3 @ X4 )
      | ~ ( r8_relat_2 @ X3 @ X4 )
      | ~ ( r4_relat_2 @ X3 @ X4 )
      | ~ ( r6_relat_2 @ X3 @ X4 )
      | ~ ( r1_wellord1 @ X3 @ X4 )
      | ( r2_wellord1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
      <=> ( v2_wellord1 @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ~ ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ( v2_wellord1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B )
    | ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ( ( ( v1_relat_2 @ A )
                   => ( v1_relat_2 @ B ) )
                  & ( ( v8_relat_2 @ A )
                   => ( v8_relat_2 @ B ) )
                  & ( ( v6_relat_2 @ A )
                   => ( v6_relat_2 @ B ) )
                  & ( ( v4_relat_2 @ A )
                   => ( v4_relat_2 @ B ) )
                  & ( ( v1_wellord1 @ A )
                   => ( v1_wellord1 @ B ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_wellord1 @ X8 )
      | ( v1_wellord1 @ X7 )
      | ~ ( r3_wellord1 @ X8 @ X7 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( r2_wellord1 @ X3 @ X5 )
      | ( r1_wellord1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i] :
      ( ~ ( r1_wellord1 @ X10 @ ( k3_relat_1 @ X10 ) )
      | ( v1_wellord1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_wellord1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( v1_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_wellord1 @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_wellord1 @ sk_B ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v6_relat_2 @ X8 )
      | ( v6_relat_2 @ X7 )
      | ~ ( r3_wellord1 @ X8 @ X7 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v6_relat_2 @ sk_B )
    | ~ ( v6_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( r2_wellord1 @ X3 @ X5 )
      | ( r6_relat_2 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ~ ( r6_relat_2 @ X1 @ ( k3_relat_1 @ X1 ) )
      | ( v6_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v6_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( v6_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v6_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v6_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['43','44','45','46','57','58'])).

thf('60',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v4_relat_2 @ X8 )
      | ( v4_relat_2 @ X7 )
      | ~ ( r3_wellord1 @ X8 @ X7 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v4_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X11: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('68',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( r2_wellord1 @ X3 @ X5 )
      | ( r4_relat_2 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v4_relat_2 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( v4_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64','65','76','77'])).

thf('79',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v8_relat_2 @ X8 )
      | ( v8_relat_2 @ X7 )
      | ~ ( r3_wellord1 @ X8 @ X7 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v8_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X11: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('87',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( r2_wellord1 @ X3 @ X5 )
      | ( r8_relat_2 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X2: $i] :
      ( ~ ( r8_relat_2 @ X2 @ ( k3_relat_1 @ X2 ) )
      | ( v8_relat_2 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v8_relat_2 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( v8_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v8_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v8_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['81','82','83','84','95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_2 @ sk_B )
    | ( v2_wellord1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','40','59','78','97'])).

thf('99',plain,(
    ~ ( v2_wellord1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ~ ( v1_relat_2 @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_2 @ X8 )
      | ( v1_relat_2 @ X7 )
      | ~ ( r3_wellord1 @ X8 @ X7 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X11: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ( r2_wellord1 @ X11 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('109',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( r2_wellord1 @ X3 @ X5 )
      | ( r1_relat_2 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X6: $i] :
      ( ~ ( r1_relat_2 @ X6 @ ( k3_relat_1 @ X6 ) )
      | ( v1_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_relat_2 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( v1_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['103','104','105','106','117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['100','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4IJ5q2dVVS
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 78 iterations in 0.035s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_wellord1_type, type, r1_wellord1: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.21/0.49  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.21/0.49  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.21/0.49  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.21/0.49  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.49  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.49  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.21/0.49  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.49  thf(t54_wellord1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49               ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.21/0.49                 ( v2_wellord1 @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( v1_relat_1 @ B ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49                  ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.21/0.49                    ( v2_wellord1 @ B ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t54_wellord1])).
% 0.21/0.49  thf('0', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t5_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v1_wellord1 @ A ) <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         (~ (v1_wellord1 @ X10)
% 0.21/0.49          | (r1_wellord1 @ X10 @ (k3_relat_1 @ X10))
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_wellord1])).
% 0.21/0.49  thf(d14_relat_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v6_relat_2 @ A ) <=> ( r6_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (~ (v6_relat_2 @ X1)
% 0.21/0.49          | (r6_relat_2 @ X1 @ (k3_relat_1 @ X1))
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d14_relat_2])).
% 0.21/0.49  thf(d12_relat_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v4_relat_2 @ A ) <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v4_relat_2 @ X0)
% 0.21/0.49          | (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.21/0.49  thf(d16_relat_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v8_relat_2 @ A ) <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X2 : $i]:
% 0.21/0.49         (~ (v8_relat_2 @ X2)
% 0.21/0.49          | (r8_relat_2 @ X2 @ (k3_relat_1 @ X2))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d16_relat_2])).
% 0.21/0.49  thf(d9_relat_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v1_relat_2 @ A ) <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (~ (v1_relat_2 @ X6)
% 0.21/0.49          | (r1_relat_2 @ X6 @ (k3_relat_1 @ X6))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.21/0.49  thf(d5_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( r2_wellord1 @ A @ B ) <=>
% 0.21/0.49           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.21/0.49             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) & 
% 0.21/0.49             ( r1_wellord1 @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (r1_relat_2 @ X3 @ X4)
% 0.21/0.49          | ~ (r8_relat_2 @ X3 @ X4)
% 0.21/0.49          | ~ (r4_relat_2 @ X3 @ X4)
% 0.21/0.49          | ~ (r6_relat_2 @ X3 @ X4)
% 0.21/0.49          | ~ (r1_wellord1 @ X3 @ X4)
% 0.21/0.49          | (r2_wellord1 @ X3 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r8_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r8_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.49  thf(t8_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | (v2_wellord1 @ X11)
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_wellord1 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v2_wellord1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_2 @ X0)
% 0.21/0.49          | ~ (v8_relat_2 @ X0)
% 0.21/0.49          | ~ (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v6_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (v1_wellord1 @ sk_B)
% 0.21/0.49        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v4_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_2 @ sk_B)
% 0.21/0.49        | (v2_wellord1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '19'])).
% 0.21/0.49  thf('21', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t53_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.21/0.49                 ( ( ( v1_relat_2 @ A ) => ( v1_relat_2 @ B ) ) & 
% 0.21/0.49                   ( ( v8_relat_2 @ A ) => ( v8_relat_2 @ B ) ) & 
% 0.21/0.49                   ( ( v6_relat_2 @ A ) => ( v6_relat_2 @ B ) ) & 
% 0.21/0.49                   ( ( v4_relat_2 @ A ) => ( v4_relat_2 @ B ) ) & 
% 0.21/0.49                   ( ( v1_wellord1 @ A ) => ( v1_wellord1 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_wellord1 @ X8)
% 0.21/0.49          | (v1_wellord1 @ X7)
% 0.21/0.49          | ~ (r3_wellord1 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v1_wellord1 @ sk_B)
% 0.21/0.49        | ~ (v1_wellord1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, (((v1_wellord1 @ sk_B) | ~ (v1_wellord1 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.21/0.49  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X11)
% 0.21/0.49          | (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X3 @ X5)
% 0.21/0.49          | (r1_wellord1 @ X3 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_wellord1 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         (~ (r1_wellord1 @ X10 @ (k3_relat_1 @ X10))
% 0.21/0.49          | (v1_wellord1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_wellord1])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v1_wellord1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_wellord1 @ X0) | ~ (v2_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('37', plain, ((~ (v2_wellord1 @ sk_A) | (v1_wellord1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.49  thf('38', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, ((v1_wellord1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ((v1_wellord1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '39'])).
% 0.21/0.49  thf('41', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v6_relat_2 @ X8)
% 0.21/0.49          | (v6_relat_2 @ X7)
% 0.21/0.49          | ~ (r3_wellord1 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v6_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v6_relat_2 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X11)
% 0.21/0.49          | (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X3 @ X5)
% 0.21/0.49          | (r6_relat_2 @ X3 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r6_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (~ (r6_relat_2 @ X1 @ (k3_relat_1 @ X1))
% 0.21/0.49          | (v6_relat_2 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d14_relat_2])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v6_relat_2 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v6_relat_2 @ X0) | ~ (v2_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.49  thf('55', plain, ((~ (v2_wellord1 @ sk_A) | (v6_relat_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '54'])).
% 0.21/0.49  thf('56', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain, ((v6_relat_2 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, ((v6_relat_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['43', '44', '45', '46', '57', '58'])).
% 0.21/0.49  thf('60', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v4_relat_2 @ X8)
% 0.21/0.49          | (v4_relat_2 @ X7)
% 0.21/0.49          | ~ (r3_wellord1 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v4_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v4_relat_2 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X11)
% 0.21/0.49          | (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X3 @ X5)
% 0.21/0.49          | (r4_relat_2 @ X3 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r4_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | (v4_relat_2 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v4_relat_2 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v4_relat_2 @ X0) | ~ (v2_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.49  thf('74', plain, ((~ (v2_wellord1 @ sk_A) | (v4_relat_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '73'])).
% 0.21/0.49  thf('75', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain, ((v4_relat_2 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('78', plain, ((v4_relat_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['62', '63', '64', '65', '76', '77'])).
% 0.21/0.49  thf('79', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v8_relat_2 @ X8)
% 0.21/0.49          | (v8_relat_2 @ X7)
% 0.21/0.49          | ~ (r3_wellord1 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v8_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v8_relat_2 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.49  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X11)
% 0.21/0.49          | (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('87', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X3 @ X5)
% 0.21/0.49          | (r8_relat_2 @ X3 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('88', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r8_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.49  thf('89', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r8_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (![X2 : $i]:
% 0.21/0.49         (~ (r8_relat_2 @ X2 @ (k3_relat_1 @ X2))
% 0.21/0.49          | (v8_relat_2 @ X2)
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d16_relat_2])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v8_relat_2 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v8_relat_2 @ X0) | ~ (v2_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.49  thf('93', plain, ((~ (v2_wellord1 @ sk_A) | (v8_relat_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['85', '92'])).
% 0.21/0.49  thf('94', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('95', plain, ((v8_relat_2 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.49  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('97', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['81', '82', '83', '84', '95', '96'])).
% 0.21/0.49  thf('98', plain, ((~ (v1_relat_2 @ sk_B) | (v2_wellord1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '40', '59', '78', '97'])).
% 0.21/0.49  thf('99', plain, (~ (v2_wellord1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('100', plain, (~ (v1_relat_2 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['98', '99'])).
% 0.21/0.49  thf('101', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('102', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_2 @ X8)
% 0.21/0.49          | (v1_relat_2 @ X7)
% 0.21/0.49          | ~ (r3_wellord1 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.49  thf('103', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v1_relat_2 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_2 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.49  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('107', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('108', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X11)
% 0.21/0.49          | (r2_wellord1 @ X11 @ (k3_relat_1 @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.21/0.49  thf('109', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_wellord1 @ X3 @ X5)
% 0.21/0.49          | (r1_relat_2 @ X3 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.49  thf('110', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.49  thf('111', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['110'])).
% 0.21/0.49  thf('112', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (~ (r1_relat_2 @ X6 @ (k3_relat_1 @ X6))
% 0.21/0.49          | (v1_relat_2 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.21/0.49  thf('113', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v2_wellord1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v1_relat_2 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.49  thf('114', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_relat_2 @ X0) | ~ (v2_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['113'])).
% 0.21/0.49  thf('115', plain, ((~ (v2_wellord1 @ sk_A) | (v1_relat_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['107', '114'])).
% 0.21/0.49  thf('116', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('117', plain, ((v1_relat_2 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['115', '116'])).
% 0.21/0.49  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('119', plain, ((v1_relat_2 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['103', '104', '105', '106', '117', '118'])).
% 0.21/0.49  thf('120', plain, ($false), inference('demod', [status(thm)], ['100', '119'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
