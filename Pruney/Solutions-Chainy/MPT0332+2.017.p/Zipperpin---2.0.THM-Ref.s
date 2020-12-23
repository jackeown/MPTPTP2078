%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W3C5008gQ5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:09 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 570 expanded)
%              Number of leaves         :   19 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  618 (4355 expanded)
%              Number of equality atoms :   70 ( 555 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ X42 @ X41 )
      | ( X41
        = ( k4_xboole_0 @ X41 @ ( k2_tarski @ X40 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','41'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','58'])).

thf('60',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W3C5008gQ5
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 609 iterations in 0.283s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.73  thf(t145_zfmisc_1, conjecture,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.56/0.73          ( ( C ) !=
% 0.56/0.73            ( k4_xboole_0 @
% 0.56/0.73              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.56/0.73              ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.73        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.56/0.73             ( ( C ) !=
% 0.56/0.73               ( k4_xboole_0 @
% 0.56/0.73                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.56/0.73                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 0.56/0.73  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t144_zfmisc_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.56/0.73          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.56/0.73  thf('1', plain,
% 0.56/0.73      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.56/0.73         ((r2_hidden @ X40 @ X41)
% 0.56/0.73          | (r2_hidden @ X42 @ X41)
% 0.56/0.73          | ((X41) = (k4_xboole_0 @ X41 @ (k2_tarski @ X40 @ X42))))),
% 0.56/0.73      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.56/0.73  thf('2', plain,
% 0.56/0.73      (((sk_C)
% 0.56/0.73         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.56/0.73             (k2_tarski @ sk_A @ sk_B)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t95_xboole_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( k3_xboole_0 @ A @ B ) =
% 0.56/0.73       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.56/0.73  thf('3', plain,
% 0.56/0.73      (![X9 : $i, X10 : $i]:
% 0.56/0.73         ((k3_xboole_0 @ X9 @ X10)
% 0.56/0.73           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.56/0.73  thf(t91_xboole_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.56/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.56/0.73  thf('4', plain,
% 0.56/0.73      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.73           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.73  thf('5', plain,
% 0.56/0.73      (![X9 : $i, X10 : $i]:
% 0.56/0.73         ((k3_xboole_0 @ X9 @ X10)
% 0.56/0.73           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ (k2_xboole_0 @ X9 @ X10))))),
% 0.56/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.56/0.73  thf(t92_xboole_1, axiom,
% 0.56/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.56/0.73  thf('6', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.56/0.73  thf('7', plain,
% 0.56/0.73      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.73           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.73  thf('8', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['6', '7'])).
% 0.56/0.73  thf('9', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.56/0.73  thf('10', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['6', '7'])).
% 0.56/0.73  thf('11', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.56/0.73  thf(t5_boole, axiom,
% 0.56/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.73  thf('12', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.56/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.73  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.56/0.73  thf('14', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.56/0.73  thf('15', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['5', '14'])).
% 0.56/0.73  thf(t100_xboole_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.56/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.56/0.73  thf('18', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.56/0.73  thf('19', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X1 @ X0)
% 0.56/0.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['17', '18'])).
% 0.56/0.73  thf(t98_xboole_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.56/0.73  thf('20', plain,
% 0.56/0.73      (![X11 : $i, X12 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X11 @ X12)
% 0.56/0.73           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.56/0.73  thf('21', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.73  thf('22', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.73  thf(t21_xboole_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.56/0.73  thf('23', plain,
% 0.56/0.73      (![X2 : $i, X3 : $i]:
% 0.56/0.73         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.56/0.73      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.56/0.73  thf('24', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.56/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.73  thf('25', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.56/0.73           = (k5_xboole_0 @ X0 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.73  thf('26', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.56/0.73  thf('27', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.56/0.73      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.73  thf('28', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['22', '27'])).
% 0.56/0.73  thf('29', plain,
% 0.56/0.73      (![X11 : $i, X12 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X11 @ X12)
% 0.56/0.73           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.56/0.73  thf('30', plain,
% 0.56/0.73      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.73           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.73  thf('31', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.56/0.73  thf('32', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.56/0.73           = (k1_xboole_0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.56/0.73  thf('33', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.56/0.73  thf('34', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['32', '33'])).
% 0.56/0.73  thf('35', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.56/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.73  thf('36', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.56/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.56/0.73  thf('37', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (X1))),
% 0.56/0.73      inference('sup+', [status(thm)], ['29', '36'])).
% 0.56/0.73  thf('38', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ k1_xboole_0 @ 
% 0.56/0.73           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 0.56/0.73           = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['28', '37'])).
% 0.56/0.73  thf('39', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.73  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.56/0.73  thf('41', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.56/0.73  thf('42', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.73      inference('sup+', [status(thm)], ['21', '41'])).
% 0.56/0.73  thf('43', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.56/0.73      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.73  thf('44', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X1 @ X0)
% 0.56/0.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['17', '18'])).
% 0.56/0.73  thf('45', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['43', '44'])).
% 0.56/0.73  thf('46', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.56/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.56/0.73  thf('47', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.56/0.73  thf('48', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['46', '47'])).
% 0.56/0.73  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.56/0.73  thf('50', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.73           = (k2_xboole_0 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['45', '48', '49'])).
% 0.56/0.73  thf('51', plain,
% 0.56/0.73      (![X11 : $i, X12 : $i]:
% 0.56/0.73         ((k2_xboole_0 @ X11 @ X12)
% 0.56/0.73           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.56/0.73  thf('52', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.56/0.73  thf('53', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.56/0.73           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['51', '52'])).
% 0.56/0.73  thf('54', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.56/0.73           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['50', '53'])).
% 0.56/0.73  thf('55', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0)
% 0.56/0.73           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['42', '54'])).
% 0.56/0.73  thf('56', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.74           = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['21', '41'])).
% 0.56/0.74  thf('57', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.56/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['15', '16'])).
% 0.56/0.74  thf('58', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.56/0.74  thf('59', plain,
% 0.56/0.74      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.56/0.74      inference('demod', [status(thm)], ['2', '58'])).
% 0.56/0.74  thf('60', plain,
% 0.56/0.74      ((((sk_C) != (sk_C))
% 0.56/0.74        | (r2_hidden @ sk_B @ sk_C)
% 0.56/0.74        | (r2_hidden @ sk_A @ sk_C))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '59'])).
% 0.56/0.74  thf('61', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.56/0.74      inference('simplify', [status(thm)], ['60'])).
% 0.56/0.74  thf('62', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('63', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.56/0.74      inference('clc', [status(thm)], ['61', '62'])).
% 0.56/0.74  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
