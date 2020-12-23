%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wGdVDLtLUc

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:49 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 295 expanded)
%              Number of leaves         :   21 (  90 expanded)
%              Depth                    :   20
%              Number of atoms          :  614 (3184 expanded)
%              Number of equality atoms :   60 ( 235 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X25 ) @ ( k1_setfam_1 @ X26 ) ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( ( k3_xboole_0 @ X24 @ ( k1_tarski @ X23 ) )
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('51',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['35','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['8','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','54'])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['35','51'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wGdVDLtLUc
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 275 iterations in 0.149s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(t12_setfam_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.60         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t69_enumset1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.60  thf('1', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(t41_enumset1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k2_tarski @ A @ B ) =
% 0.40/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i]:
% 0.40/0.60         ((k2_tarski @ X15 @ X16)
% 0.40/0.60           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_tarski @ X0 @ X1)
% 0.40/0.60           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf('4', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(t11_setfam_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.60  thf('5', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.40/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.60  thf('6', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf(t10_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.40/0.60            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X25 : $i, X26 : $i]:
% 0.40/0.60         (((X25) = (k1_xboole_0))
% 0.40/0.60          | ((k1_setfam_1 @ (k2_xboole_0 @ X25 @ X26))
% 0.40/0.60              = (k3_xboole_0 @ (k1_setfam_1 @ X25) @ (k1_setfam_1 @ X26)))
% 0.40/0.60          | ((X26) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.40/0.60            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.40/0.60          | ((X1) = (k1_xboole_0))
% 0.40/0.60          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(d4_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.60       ( ![D:$i]:
% 0.40/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.40/0.60         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.40/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.40/0.60          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.60      inference('eq_fact', [status(thm)], ['10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.40/0.60         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.40/0.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.40/0.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.40/0.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.40/0.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.40/0.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.40/0.60          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.40/0.60          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.40/0.60         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.40/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.40/0.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.60      inference('eq_fact', [status(thm)], ['15'])).
% 0.40/0.60  thf('17', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['14', '16'])).
% 0.40/0.60  thf(d7_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X6 : $i, X8 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('20', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.60  thf(t4_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X9 @ X10)
% 0.40/0.60          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.60          | (r2_hidden @ X4 @ X1)
% 0.40/0.60          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.60         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['21', '23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.40/0.60          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.40/0.60          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['20', '26'])).
% 0.40/0.60  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['14', '16'])).
% 0.40/0.60  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.40/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X6 : $i, X7 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(l29_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.40/0.60       ( r2_hidden @ B @ A ) ))).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X23 : $i, X24 : $i]:
% 0.40/0.60         ((r2_hidden @ X23 @ X24)
% 0.40/0.60          | ((k3_xboole_0 @ X24 @ (k1_tarski @ X23)) != (k1_tarski @ X23)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (k1_tarski @ X0))
% 0.40/0.60          | (r2_hidden @ X0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '34'])).
% 0.40/0.60  thf('36', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X9 @ X10)
% 0.40/0.60          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.60          | (r2_hidden @ X4 @ X2)
% 0.40/0.60          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.60         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['37', '39'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.40/0.60          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.60          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['36', '42'])).
% 0.40/0.60  thf('44', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['14', '16'])).
% 0.40/0.60  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X6 : $i, X7 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.40/0.60          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.60  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.60  thf('51', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.60  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['35', '51'])).
% 0.40/0.60  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['9', '52'])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X1) = (k1_xboole_0))
% 0.40/0.60          | ((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.40/0.60              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.40/0.60      inference('clc', [status(thm)], ['8', '53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.40/0.60            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.40/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['3', '54'])).
% 0.40/0.60  thf('56', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.40/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.60          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.60  thf('58', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['35', '51'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['57', '58'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['0', '59'])).
% 0.40/0.60  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
