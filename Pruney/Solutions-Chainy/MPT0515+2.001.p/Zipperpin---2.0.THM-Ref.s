%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5D0WPN0MUY

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:33 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  700 (1363 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t115_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
        <=> ( ( r2_hidden @ A @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_relat_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ( X9
       != ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k2_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) @ sk_A ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k2_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','18','37','38','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5D0WPN0MUY
% 0.16/0.39  % Computer   : n010.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 11:19:45 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 37 iterations in 0.021s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.53  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.25/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.25/0.53  thf(t115_relat_1, conjecture,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( v1_relat_1 @ C ) =>
% 0.25/0.53       ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.25/0.53         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.53        ( ( v1_relat_1 @ C ) =>
% 0.25/0.53          ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.25/0.53            ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t115_relat_1])).
% 0.25/0.53  thf('0', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ sk_B)
% 0.25/0.53        | (r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('1', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.25/0.53       ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf(dt_k8_relat_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.25/0.53  thf('2', plain,
% 0.25/0.53      (![X13 : $i, X14 : $i]:
% 0.25/0.53         ((v1_relat_1 @ (k8_relat_1 @ X13 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.25/0.53  thf('3', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf(d5_relat_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.25/0.53       ( ![C:$i]:
% 0.25/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.25/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.25/0.53  thf('4', plain,
% 0.25/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X10 @ X8) @ X10) @ X8)
% 0.25/0.53          | ((X9) != (k2_relat_1 @ X8)))),
% 0.25/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.25/0.53  thf('5', plain,
% 0.25/0.53      (![X8 : $i, X10 : $i]:
% 0.25/0.53         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X10 @ X8) @ X10) @ X8)
% 0.25/0.53          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X8)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.25/0.53  thf('6', plain,
% 0.25/0.53      (((r2_hidden @ 
% 0.25/0.53         (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53         (k8_relat_1 @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.25/0.53  thf(d12_relat_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( v1_relat_1 @ B ) =>
% 0.25/0.53       ( ![C:$i]:
% 0.25/0.53         ( ( v1_relat_1 @ C ) =>
% 0.25/0.53           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.25/0.53             ( ![D:$i,E:$i]:
% 0.25/0.53               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.25/0.53                 ( ( r2_hidden @ E @ A ) & 
% 0.25/0.53                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.25/0.53  thf('7', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X0)
% 0.25/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | (r2_hidden @ X5 @ X1)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.25/0.53          | ~ (v1_relat_1 @ X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.25/0.53  thf('8', plain,
% 0.25/0.53      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | (r2_hidden @ X5 @ X1)
% 0.25/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.25/0.53  thf('9', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.25/0.53         | (r2_hidden @ sk_A @ sk_B)
% 0.25/0.53         | ~ (v1_relat_1 @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.25/0.53  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.25/0.53         | (r2_hidden @ sk_A @ sk_B)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.25/0.53  thf('12', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ sk_B)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['2', '11'])).
% 0.25/0.53  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('14', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ sk_B))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('15', plain,
% 0.25/0.53      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.25/0.53        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.25/0.53        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('16', plain,
% 0.25/0.53      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.25/0.53      inference('split', [status(esa)], ['15'])).
% 0.25/0.53  thf('17', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.25/0.53       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.25/0.53  thf('18', plain,
% 0.25/0.53      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.25/0.53       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))) | 
% 0.25/0.53       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['15'])).
% 0.25/0.53  thf('19', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.25/0.53        | (r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('split', [status(esa)], ['20'])).
% 0.25/0.53  thf('22', plain,
% 0.25/0.53      (![X8 : $i, X10 : $i]:
% 0.25/0.53         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X10 @ X8) @ X10) @ X8)
% 0.25/0.53          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X8)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.25/0.53  thf('23', plain,
% 0.25/0.53      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_C_1) @ sk_A) @ sk_C_1))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.53  thf('24', plain,
% 0.25/0.53      (![X13 : $i, X14 : $i]:
% 0.25/0.53         ((v1_relat_1 @ (k8_relat_1 @ X13 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.25/0.53  thf('25', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X0)
% 0.25/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X1)
% 0.25/0.53          | ~ (v1_relat_1 @ X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.25/0.53  thf('26', plain,
% 0.25/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X1)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.25/0.53  thf('27', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X0)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.25/0.53          | ~ (r2_hidden @ X2 @ X1)
% 0.25/0.53          | ~ (v1_relat_1 @ X0))),
% 0.25/0.53      inference('sup-', [status(thm)], ['24', '26'])).
% 0.25/0.53  thf('28', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X2 @ X1)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.25/0.53          | ~ (v1_relat_1 @ X0))),
% 0.25/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.25/0.53  thf('29', plain,
% 0.25/0.53      ((![X0 : $i]:
% 0.25/0.53          (~ (v1_relat_1 @ sk_C_1)
% 0.25/0.53           | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_C_1) @ sk_A) @ 
% 0.25/0.53              (k8_relat_1 @ X0 @ sk_C_1))
% 0.25/0.53           | ~ (r2_hidden @ sk_A @ X0)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['23', '28'])).
% 0.25/0.53  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('31', plain,
% 0.25/0.53      ((![X0 : $i]:
% 0.25/0.53          ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_C_1) @ sk_A) @ 
% 0.25/0.53            (k8_relat_1 @ X0 @ sk_C_1))
% 0.25/0.53           | ~ (r2_hidden @ sk_A @ X0)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.25/0.53  thf('32', plain,
% 0.25/0.53      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_C_1) @ sk_A) @ 
% 0.25/0.53         (k8_relat_1 @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ sk_B)) & 
% 0.25/0.53             ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['19', '31'])).
% 0.25/0.53  thf('33', plain,
% 0.25/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.25/0.53         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.25/0.53          | (r2_hidden @ X7 @ X9)
% 0.25/0.53          | ((X9) != (k2_relat_1 @ X8)))),
% 0.25/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.25/0.53  thf('34', plain,
% 0.25/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.53         ((r2_hidden @ X7 @ (k2_relat_1 @ X8))
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.25/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.25/0.53  thf('35', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ sk_B)) & 
% 0.25/0.53             ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['32', '34'])).
% 0.25/0.53  thf('36', plain,
% 0.25/0.53      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))))
% 0.25/0.53         <= (~
% 0.25/0.53             ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('split', [status(esa)], ['15'])).
% 0.25/0.53  thf('37', plain,
% 0.25/0.53      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.25/0.53       ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))) | 
% 0.25/0.53       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.25/0.53  thf('38', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))) | 
% 0.25/0.53       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['20'])).
% 0.25/0.53  thf('39', plain,
% 0.25/0.53      (![X13 : $i, X14 : $i]:
% 0.25/0.53         ((v1_relat_1 @ (k8_relat_1 @ X13 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.25/0.53  thf('40', plain,
% 0.25/0.53      (((r2_hidden @ 
% 0.25/0.53         (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53         (k8_relat_1 @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.25/0.53  thf('41', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X0)
% 0.25/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.25/0.53          | ~ (v1_relat_1 @ X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.25/0.53  thf('42', plain,
% 0.25/0.53      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.25/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.25/0.53  thf('43', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.25/0.53         | (r2_hidden @ 
% 0.25/0.53            (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53            sk_C_1)
% 0.25/0.53         | ~ (v1_relat_1 @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['40', '42'])).
% 0.25/0.53  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('45', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.25/0.53         | (r2_hidden @ 
% 0.25/0.53            (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53            sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.25/0.53  thf('46', plain,
% 0.25/0.53      (((~ (v1_relat_1 @ sk_C_1)
% 0.25/0.53         | (r2_hidden @ 
% 0.25/0.53            (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53            sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['39', '45'])).
% 0.25/0.53  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('48', plain,
% 0.25/0.53      (((r2_hidden @ 
% 0.25/0.53         (k4_tarski @ (sk_D_2 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_1)) @ sk_A) @ 
% 0.25/0.53         sk_C_1))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.53  thf('49', plain,
% 0.25/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.53         ((r2_hidden @ X7 @ (k2_relat_1 @ X8))
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.25/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.25/0.53  thf('50', plain,
% 0.25/0.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.25/0.53         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.25/0.53  thf('51', plain,
% 0.25/0.53      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.25/0.53         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.25/0.53      inference('split', [status(esa)], ['15'])).
% 0.25/0.53  thf('52', plain,
% 0.25/0.53      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))) | 
% 0.25/0.53       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.25/0.53  thf('53', plain, ($false),
% 0.25/0.53      inference('sat_resolution*', [status(thm)],
% 0.25/0.53                ['1', '17', '18', '37', '38', '52'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.25/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
