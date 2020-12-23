%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0515+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v8szhvccnf

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
