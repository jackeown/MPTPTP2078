%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jY0LYO7vre

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 114 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  607 ( 821 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('1',plain,(
    ! [X22: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ~ ( r1_tarski @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t22_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ~ ( v3_ordinal1 @ X19 )
      | ~ ( v1_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X9 @ X10 )
      | ( r1_ordinal1 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_ordinal1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_ordinal1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ X0 )
      | ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( v1_ordinal1 @ X13 )
      | ~ ( r1_tarski @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','57'])).

thf(t30_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_ordinal1])).

thf('59',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jY0LYO7vre
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:39:55 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 317 iterations in 0.270s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.74  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.53/0.74  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.53/0.74  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.53/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.74  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.74  thf(t29_ordinal1, axiom,
% 0.53/0.74    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (![X22 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.53/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X22 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.53/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.53/0.74  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.53/0.74  thf('2', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.53/0.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.53/0.74  thf(d2_ordinal1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_ordinal1 @ A ) <=>
% 0.53/0.74       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X13 : $i]: ((v1_ordinal1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf(t94_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.53/0.74       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.53/0.74          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X11 @ X12)
% 0.53/0.74          | (r1_tarski @ X11 @ X12)
% 0.53/0.74          | ~ (v1_ordinal1 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.53/0.74          | ~ (v1_ordinal1 @ X0)
% 0.53/0.74          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         ((r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.53/0.74          | ~ (r1_tarski @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.53/0.74          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.53/0.74  thf(d3_tarski, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.74          | (r2_hidden @ X0 @ X2)
% 0.53/0.74          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | (r2_hidden @ X1 @ X0)
% 0.53/0.74          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.53/0.74          | (r2_hidden @ (sk_B @ (k3_tarski @ X0)) @ X0)
% 0.53/0.74          | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['3', '11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X1 : $i, X3 : $i]:
% 0.53/0.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X1 : $i, X3 : $i]:
% 0.53/0.74         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.74  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.74      inference('simplify', [status(thm)], ['15'])).
% 0.53/0.74  thf(t56_setfam_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.53/0.74       ( r1_tarski @ C @ B ) ))).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.74         (~ (r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.53/0.74          | ~ (r2_hidden @ X8 @ X6)
% 0.53/0.74          | (r1_tarski @ X8 @ X7))),
% 0.53/0.74      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ (k3_tarski @ X0))
% 0.53/0.74          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['12', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X13 : $i]: ((v1_ordinal1 @ X13) | ~ (r1_tarski @ (sk_B @ X13) @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X0 : $i]: ((v1_ordinal1 @ (k3_tarski @ X0)) | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('clc', [status(thm)], ['19', '20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.53/0.74  thf(t22_ordinal1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_ordinal1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( v3_ordinal1 @ B ) =>
% 0.53/0.74           ( ![C:$i]:
% 0.53/0.74             ( ( v3_ordinal1 @ C ) =>
% 0.53/0.74               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.53/0.74                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X17)
% 0.53/0.74          | ~ (r1_tarski @ X18 @ X17)
% 0.53/0.74          | ~ (r2_hidden @ X17 @ X19)
% 0.53/0.74          | (r2_hidden @ X18 @ X19)
% 0.53/0.74          | ~ (v3_ordinal1 @ X19)
% 0.53/0.74          | ~ (v1_ordinal1 @ X18))),
% 0.53/0.74      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ X1)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.53/0.74          | ~ (r2_hidden @ X0 @ X1)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (r2_hidden @ X0 @ X1)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.53/0.74          | ~ (v3_ordinal1 @ X1)
% 0.53/0.74          | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X1)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.53/0.74          | ~ (r2_hidden @ X0 @ X1)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['25'])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['2', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_ordinal1 @ X0)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X13 : $i]: ((v1_ordinal1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf(t23_ordinal1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ X20)
% 0.53/0.74          | ~ (v3_ordinal1 @ X21)
% 0.53/0.74          | ~ (r2_hidden @ X20 @ X21))),
% 0.53/0.74      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v3_ordinal1 @ (sk_B @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v3_ordinal1 @ (sk_B @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.74  thf(connectedness_r1_ordinal1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.53/0.74       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X9 : $i, X10 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X9)
% 0.53/0.74          | ~ (v3_ordinal1 @ X10)
% 0.53/0.74          | (r1_ordinal1 @ X9 @ X10)
% 0.53/0.74          | (r1_ordinal1 @ X10 @ X9))),
% 0.53/0.74      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.53/0.74  thf(redefinition_r1_ordinal1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.53/0.74       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X14)
% 0.53/0.74          | ~ (v3_ordinal1 @ X15)
% 0.53/0.74          | (r1_tarski @ X14 @ X15)
% 0.53/0.74          | ~ (r1_ordinal1 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r1_ordinal1 @ X0 @ X1)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X1)
% 0.53/0.74          | (r1_tarski @ X1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r1_tarski @ X1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X1)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (r1_ordinal1 @ X0 @ X1))),
% 0.53/0.74      inference('simplify', [status(thm)], ['36'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (![X13 : $i]: ((v1_ordinal1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf(t7_ordinal1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.53/0.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r1_ordinal1 @ (sk_B @ X0) @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['37', '40'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (r1_ordinal1 @ (sk_B @ X0) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['33', '41'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r1_ordinal1 @ (sk_B @ X0) @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X14)
% 0.53/0.74          | ~ (v3_ordinal1 @ X15)
% 0.53/0.74          | (r1_tarski @ X14 @ X15)
% 0.53/0.74          | ~ (r1_ordinal1 @ X14 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | (r1_tarski @ (sk_B @ X0) @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ (sk_B @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.53/0.74          | (r1_tarski @ (sk_B @ X0) @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | (r1_tarski @ (sk_B @ X0) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['32', '46'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r1_tarski @ (sk_B @ X0) @ X0)
% 0.53/0.74          | (v1_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['47'])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      (![X13 : $i]: ((v1_ordinal1 @ X13) | ~ (r1_tarski @ (sk_B @ X13) @ X13))),
% 0.53/0.74      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.53/0.74  thf('50', plain, (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v1_ordinal1 @ X0))),
% 0.53/0.74      inference('clc', [status(thm)], ['48', '49'])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 0.53/0.74      inference('clc', [status(thm)], ['29', '50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ X20)
% 0.53/0.74          | ~ (v3_ordinal1 @ X21)
% 0.53/0.74          | ~ (r2_hidden @ X20 @ X21))),
% 0.53/0.74      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v3_ordinal1 @ X0)
% 0.53/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.53/0.74          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.74  thf('54', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.53/0.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ X20)
% 0.53/0.74          | ~ (v3_ordinal1 @ X21)
% 0.53/0.74          | ~ (r2_hidden @ X20 @ X21))),
% 0.53/0.74      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (![X0 : $i]: (~ (v3_ordinal1 @ (k1_ordinal1 @ X0)) | (v3_ordinal1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.53/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.53/0.74      inference('clc', [status(thm)], ['53', '56'])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '57'])).
% 0.53/0.74  thf(t30_ordinal1, conjecture,
% 0.53/0.74    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.53/0.74  thf('59', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('60', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.53/0.74  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('62', plain, ($false), inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
