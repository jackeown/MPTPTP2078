%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArgGwx9BCt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:45 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 139 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  584 (1293 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k8_relat_1 @ X22 @ X23 ) @ ( k8_relat_1 @ X22 @ X21 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_2 ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( ( k8_relat_1 @ X19 @ ( k8_relat_1 @ X18 @ X20 ) )
        = ( k8_relat_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X16 @ X17 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k4_tarski @ ( sk_C @ X11 ) @ ( sk_D_1 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k4_tarski @ ( sk_C @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ( ( sk_B @ X13 )
       != ( k4_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X16 @ X17 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D_2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D_2 )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_D_2 )
      = ( k8_relat_1 @ sk_B_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['9','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D_2 )
      = ( k8_relat_1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C_1 )
    = ( k8_relat_1 @ sk_B_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X16 @ X17 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k8_relat_1 @ X22 @ X23 ) @ ( k8_relat_1 @ X22 @ X21 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArgGwx9BCt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.53  % Solved by: fo/fo7.sh
% 1.35/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.53  % done 1604 iterations in 1.076s
% 1.35/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.53  % SZS output start Refutation
% 1.35/1.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.35/1.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.35/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.53  thf(sk_C_type, type, sk_C: $i > $i).
% 1.35/1.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.35/1.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.35/1.53  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 1.35/1.53  thf(sk_B_type, type, sk_B: $i > $i).
% 1.35/1.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.35/1.53  thf(t133_relat_1, conjecture,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ C ) =>
% 1.35/1.53       ( ![D:$i]:
% 1.35/1.53         ( ( v1_relat_1 @ D ) =>
% 1.35/1.53           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.35/1.53             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 1.35/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.53    (~( ![A:$i,B:$i,C:$i]:
% 1.35/1.53        ( ( v1_relat_1 @ C ) =>
% 1.35/1.53          ( ![D:$i]:
% 1.35/1.53            ( ( v1_relat_1 @ D ) =>
% 1.35/1.53              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.35/1.53                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 1.35/1.53    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 1.35/1.53  thf('0', plain,
% 1.35/1.53      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.35/1.53          (k8_relat_1 @ sk_B_1 @ sk_D_2))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('1', plain, ((r1_tarski @ sk_C_1 @ sk_D_2)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(t132_relat_1, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ B ) =>
% 1.35/1.53       ( ![C:$i]:
% 1.35/1.53         ( ( v1_relat_1 @ C ) =>
% 1.35/1.53           ( ( r1_tarski @ B @ C ) =>
% 1.35/1.53             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 1.35/1.53  thf('2', plain,
% 1.35/1.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X21)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X22 @ X23) @ (k8_relat_1 @ X22 @ X21))
% 1.35/1.53          | ~ (r1_tarski @ X23 @ X21)
% 1.35/1.53          | ~ (v1_relat_1 @ X23))),
% 1.35/1.53      inference('cnf', [status(esa)], [t132_relat_1])).
% 1.35/1.53  thf('3', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ sk_C_1)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ 
% 1.35/1.53             (k8_relat_1 @ X0 @ sk_D_2))
% 1.35/1.53          | ~ (v1_relat_1 @ sk_D_2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['1', '2'])).
% 1.35/1.53  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('5', plain, ((v1_relat_1 @ sk_D_2)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('6', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ (k8_relat_1 @ X0 @ sk_D_2))),
% 1.35/1.53      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.35/1.53  thf('7', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(t129_relat_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ C ) =>
% 1.35/1.53       ( ( r1_tarski @ A @ B ) =>
% 1.35/1.53         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 1.35/1.53  thf('8', plain,
% 1.35/1.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.35/1.53         (~ (r1_tarski @ X18 @ X19)
% 1.35/1.53          | ~ (v1_relat_1 @ X20)
% 1.35/1.53          | ((k8_relat_1 @ X19 @ (k8_relat_1 @ X18 @ X20))
% 1.35/1.53              = (k8_relat_1 @ X18 @ X20)))),
% 1.35/1.53      inference('cnf', [status(esa)], [t129_relat_1])).
% 1.35/1.53  thf('9', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         (((k8_relat_1 @ sk_B_1 @ (k8_relat_1 @ sk_A @ X0))
% 1.35/1.53            = (k8_relat_1 @ sk_A @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0))),
% 1.35/1.53      inference('sup-', [status(thm)], ['7', '8'])).
% 1.35/1.53  thf(t117_relat_1, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 1.35/1.53  thf('10', plain,
% 1.35/1.53      (![X16 : $i, X17 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X16 @ X17) @ X17) | ~ (v1_relat_1 @ X17))),
% 1.35/1.53      inference('cnf', [status(esa)], [t117_relat_1])).
% 1.35/1.53  thf(t28_xboole_1, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.35/1.53  thf('11', plain,
% 1.35/1.53      (![X9 : $i, X10 : $i]:
% 1.35/1.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.35/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.53  thf('12', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0)
% 1.35/1.53          | ((k3_xboole_0 @ (k8_relat_1 @ X1 @ X0) @ X0)
% 1.35/1.53              = (k8_relat_1 @ X1 @ X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.53  thf(d1_relat_1, axiom,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ A ) <=>
% 1.35/1.53       ( ![B:$i]:
% 1.35/1.53         ( ~( ( r2_hidden @ B @ A ) & 
% 1.35/1.53              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.35/1.53  thf('13', plain,
% 1.35/1.53      (![X13 : $i]: ((v1_relat_1 @ X13) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.35/1.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.35/1.53  thf(d4_xboole_0, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.35/1.53       ( ![D:$i]:
% 1.35/1.53         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.35/1.53  thf('14', plain,
% 1.35/1.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.35/1.53         (~ (r2_hidden @ X4 @ X3)
% 1.35/1.53          | (r2_hidden @ X4 @ X2)
% 1.35/1.53          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.35/1.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.53  thf('15', plain,
% 1.35/1.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.35/1.53         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.35/1.53      inference('simplify', [status(thm)], ['14'])).
% 1.35/1.53  thf('16', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.35/1.53          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.35/1.53      inference('sup-', [status(thm)], ['13', '15'])).
% 1.35/1.53  thf('17', plain,
% 1.35/1.53      (![X11 : $i, X12 : $i]:
% 1.35/1.53         (((X11) = (k4_tarski @ (sk_C @ X11) @ (sk_D_1 @ X11)))
% 1.35/1.53          | ~ (r2_hidden @ X11 @ X12)
% 1.35/1.53          | ~ (v1_relat_1 @ X12))),
% 1.35/1.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.35/1.53  thf('18', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0)
% 1.35/1.53          | ((sk_B @ (k3_xboole_0 @ X1 @ X0))
% 1.35/1.53              = (k4_tarski @ (sk_C @ (sk_B @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.35/1.53                 (sk_D_1 @ (sk_B @ (k3_xboole_0 @ X1 @ X0))))))),
% 1.35/1.53      inference('sup-', [status(thm)], ['16', '17'])).
% 1.35/1.53  thf('19', plain,
% 1.35/1.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.35/1.53         ((v1_relat_1 @ X13) | ((sk_B @ X13) != (k4_tarski @ X14 @ X15)))),
% 1.35/1.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.35/1.53  thf('20', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.53      inference('clc', [status(thm)], ['18', '19'])).
% 1.35/1.53  thf('21', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0)
% 1.35/1.53          | ~ (v1_relat_1 @ X0))),
% 1.35/1.53      inference('sup+', [status(thm)], ['12', '20'])).
% 1.35/1.53  thf('22', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.35/1.53      inference('simplify', [status(thm)], ['21'])).
% 1.35/1.53  thf('23', plain, ((r1_tarski @ sk_C_1 @ sk_D_2)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('24', plain,
% 1.35/1.53      (![X16 : $i, X17 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X16 @ X17) @ X17) | ~ (v1_relat_1 @ X17))),
% 1.35/1.53      inference('cnf', [status(esa)], [t117_relat_1])).
% 1.35/1.53  thf(t1_xboole_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.35/1.53       ( r1_tarski @ A @ C ) ))).
% 1.35/1.53  thf('25', plain,
% 1.35/1.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.35/1.53         (~ (r1_tarski @ X6 @ X7)
% 1.35/1.53          | ~ (r1_tarski @ X7 @ X8)
% 1.35/1.53          | (r1_tarski @ X6 @ X8))),
% 1.35/1.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.35/1.53  thf('26', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 1.35/1.53          | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.53  thf('27', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D_2)
% 1.35/1.53          | ~ (v1_relat_1 @ sk_C_1))),
% 1.35/1.53      inference('sup-', [status(thm)], ['23', '26'])).
% 1.35/1.53  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('29', plain,
% 1.35/1.53      (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D_2)),
% 1.35/1.53      inference('demod', [status(thm)], ['27', '28'])).
% 1.35/1.53  thf('30', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 1.35/1.53          | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.53  thf('31', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ sk_D_2)
% 1.35/1.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C_1)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['29', '30'])).
% 1.35/1.53  thf('32', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ sk_C_1)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 1.35/1.53             sk_D_2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['22', '31'])).
% 1.35/1.53  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('34', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ sk_D_2)),
% 1.35/1.53      inference('demod', [status(thm)], ['32', '33'])).
% 1.35/1.53  thf('35', plain,
% 1.35/1.53      (![X9 : $i, X10 : $i]:
% 1.35/1.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.35/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.53  thf('36', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         ((k3_xboole_0 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 1.35/1.53           sk_D_2) = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['34', '35'])).
% 1.35/1.53  thf('37', plain,
% 1.35/1.53      ((((k3_xboole_0 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_D_2)
% 1.35/1.53          = (k8_relat_1 @ sk_B_1 @ (k8_relat_1 @ sk_A @ sk_C_1)))
% 1.35/1.53        | ~ (v1_relat_1 @ sk_C_1))),
% 1.35/1.53      inference('sup+', [status(thm)], ['9', '36'])).
% 1.35/1.53  thf('38', plain,
% 1.35/1.53      (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D_2)),
% 1.35/1.53      inference('demod', [status(thm)], ['27', '28'])).
% 1.35/1.53  thf('39', plain,
% 1.35/1.53      (![X9 : $i, X10 : $i]:
% 1.35/1.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.35/1.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.53  thf('40', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((k3_xboole_0 @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D_2)
% 1.35/1.53           = (k8_relat_1 @ X0 @ sk_C_1))),
% 1.35/1.53      inference('sup-', [status(thm)], ['38', '39'])).
% 1.35/1.53  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('42', plain,
% 1.35/1.53      (((k8_relat_1 @ sk_A @ sk_C_1)
% 1.35/1.53         = (k8_relat_1 @ sk_B_1 @ (k8_relat_1 @ sk_A @ sk_C_1)))),
% 1.35/1.53      inference('demod', [status(thm)], ['37', '40', '41'])).
% 1.35/1.53  thf('43', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.35/1.53      inference('simplify', [status(thm)], ['21'])).
% 1.35/1.53  thf('44', plain,
% 1.35/1.53      (![X16 : $i, X17 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X16 @ X17) @ X17) | ~ (v1_relat_1 @ X17))),
% 1.35/1.53      inference('cnf', [status(esa)], [t117_relat_1])).
% 1.35/1.53  thf('45', plain,
% 1.35/1.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X21)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X22 @ X23) @ (k8_relat_1 @ X22 @ X21))
% 1.35/1.53          | ~ (r1_tarski @ X23 @ X21)
% 1.35/1.53          | ~ (v1_relat_1 @ X23))),
% 1.35/1.53      inference('cnf', [status(esa)], [t132_relat_1])).
% 1.35/1.53  thf('46', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0)
% 1.35/1.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.35/1.53             (k8_relat_1 @ X2 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0))),
% 1.35/1.53      inference('sup-', [status(thm)], ['44', '45'])).
% 1.35/1.53  thf('47', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.35/1.53           (k8_relat_1 @ X2 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0))),
% 1.35/1.53      inference('simplify', [status(thm)], ['46'])).
% 1.35/1.53  thf('48', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (~ (v1_relat_1 @ X0)
% 1.35/1.53          | ~ (v1_relat_1 @ X0)
% 1.35/1.53          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.35/1.53             (k8_relat_1 @ X2 @ X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['43', '47'])).
% 1.35/1.53  thf('49', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.35/1.53           (k8_relat_1 @ X2 @ X0))
% 1.35/1.53          | ~ (v1_relat_1 @ X0))),
% 1.35/1.53      inference('simplify', [status(thm)], ['48'])).
% 1.35/1.53  thf('50', plain,
% 1.35/1.53      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.35/1.53         (k8_relat_1 @ sk_B_1 @ sk_C_1))
% 1.35/1.53        | ~ (v1_relat_1 @ sk_C_1))),
% 1.35/1.53      inference('sup+', [status(thm)], ['42', '49'])).
% 1.35/1.53  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('52', plain,
% 1.35/1.53      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.35/1.53        (k8_relat_1 @ sk_B_1 @ sk_C_1))),
% 1.35/1.53      inference('demod', [status(thm)], ['50', '51'])).
% 1.35/1.53  thf('53', plain,
% 1.35/1.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.35/1.53         (~ (r1_tarski @ X6 @ X7)
% 1.35/1.53          | ~ (r1_tarski @ X7 @ X8)
% 1.35/1.53          | (r1_tarski @ X6 @ X8))),
% 1.35/1.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.35/1.53  thf('54', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0)
% 1.35/1.53          | ~ (r1_tarski @ (k8_relat_1 @ sk_B_1 @ sk_C_1) @ X0))),
% 1.35/1.53      inference('sup-', [status(thm)], ['52', '53'])).
% 1.35/1.53  thf('55', plain,
% 1.35/1.53      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.35/1.53        (k8_relat_1 @ sk_B_1 @ sk_D_2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['6', '54'])).
% 1.35/1.53  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.35/1.53  
% 1.35/1.53  % SZS output end Refutation
% 1.35/1.53  
% 1.35/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
