%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTl6qCocAE

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:37 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  124 (1207 expanded)
%              Number of leaves         :   17 ( 359 expanded)
%              Depth                    :   22
%              Number of atoms          :  994 (12135 expanded)
%              Number of equality atoms :   90 (1355 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('31',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('37',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('59',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('65',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['52','67'])).

thf('69',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('70',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['52','67'])).

thf('86',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,(
    sk_D_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['71','92'])).

thf('94',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['70','93'])).

thf('95',plain,(
    sk_C_1 = sk_A ),
    inference(demod,[status(thm)],['51','94'])).

thf('96',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['84','91'])).

thf('99',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['96'])).

thf('100',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B = sk_D_1 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['96'])).

thf('103',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['97','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTl6qCocAE
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.62/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.62/1.79  % Solved by: fo/fo7.sh
% 1.62/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.62/1.79  % done 728 iterations in 1.342s
% 1.62/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.62/1.79  % SZS output start Refutation
% 1.62/1.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.62/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.62/1.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.62/1.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.62/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.62/1.79  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.62/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.62/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.62/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.62/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.62/1.79  thf(t134_zfmisc_1, conjecture,
% 1.62/1.79    (![A:$i,B:$i,C:$i,D:$i]:
% 1.62/1.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.62/1.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.62/1.79         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 1.62/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.62/1.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.62/1.79        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.62/1.79          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.62/1.79            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 1.62/1.79    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 1.62/1.79  thf('0', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(d10_xboole_0, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.62/1.79  thf('1', plain,
% 1.62/1.79      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('2', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.62/1.79      inference('simplify', [status(thm)], ['1'])).
% 1.62/1.79  thf(t28_xboole_1, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.62/1.79  thf('3', plain,
% 1.62/1.79      (![X13 : $i, X14 : $i]:
% 1.62/1.79         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.62/1.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.62/1.79  thf('4', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf(t123_zfmisc_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i,D:$i]:
% 1.62/1.79     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 1.62/1.79       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.62/1.79  thf('5', plain,
% 1.62/1.79      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X21))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 1.62/1.79              (k2_zfmisc_1 @ X20 @ X21)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.62/1.79  thf('6', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['4', '5'])).
% 1.62/1.79  thf('7', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 1.62/1.79              (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['0', '6'])).
% 1.62/1.79  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('9', plain,
% 1.62/1.79      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X21))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 1.62/1.79              (k2_zfmisc_1 @ X20 @ X21)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.62/1.79  thf('10', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['8', '9'])).
% 1.62/1.79  thf('11', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 1.62/1.79         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 1.62/1.79      inference('sup+', [status(thm)], ['7', '10'])).
% 1.62/1.79  thf('12', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf(t117_zfmisc_1, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.62/1.79          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.62/1.79            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.62/1.79          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.62/1.79  thf('13', plain,
% 1.62/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.62/1.79         (((X15) = (k1_xboole_0))
% 1.62/1.79          | (r1_tarski @ X16 @ X17)
% 1.62/1.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 1.62/1.79               (k2_zfmisc_1 @ X17 @ X15)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.62/1.79  thf('14', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79             (k2_zfmisc_1 @ X0 @ sk_B))
% 1.62/1.79          | (r1_tarski @ sk_A @ X0)
% 1.62/1.79          | ((sk_B) = (k1_xboole_0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['12', '13'])).
% 1.62/1.79  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('16', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79             (k2_zfmisc_1 @ X0 @ sk_B))
% 1.62/1.79          | (r1_tarski @ sk_A @ X0))),
% 1.62/1.79      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 1.62/1.79  thf('17', plain,
% 1.62/1.79      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79           (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1)))
% 1.62/1.79        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['11', '16'])).
% 1.62/1.79  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('19', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 1.62/1.79         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 1.62/1.79      inference('sup+', [status(thm)], ['7', '10'])).
% 1.62/1.79  thf('20', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['8', '9'])).
% 1.62/1.79  thf(d3_tarski, axiom,
% 1.62/1.79    (![A:$i,B:$i]:
% 1.62/1.79     ( ( r1_tarski @ A @ B ) <=>
% 1.62/1.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.62/1.79  thf('21', plain,
% 1.62/1.79      (![X1 : $i, X3 : $i]:
% 1.62/1.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.62/1.79      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.79  thf(d4_xboole_0, axiom,
% 1.62/1.79    (![A:$i,B:$i,C:$i]:
% 1.62/1.79     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.62/1.79       ( ![D:$i]:
% 1.62/1.79         ( ( r2_hidden @ D @ C ) <=>
% 1.62/1.79           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.62/1.79  thf('22', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.62/1.79         (~ (r2_hidden @ X8 @ X7)
% 1.62/1.79          | (r2_hidden @ X8 @ X6)
% 1.62/1.79          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.62/1.79      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.62/1.79  thf('23', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.62/1.79         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.62/1.79      inference('simplify', [status(thm)], ['22'])).
% 1.62/1.79  thf('24', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.62/1.79          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['21', '23'])).
% 1.62/1.79  thf('25', plain,
% 1.62/1.79      (![X1 : $i, X3 : $i]:
% 1.62/1.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.62/1.79      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.79  thf('26', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]:
% 1.62/1.79         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.62/1.79          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['24', '25'])).
% 1.62/1.79  thf('27', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.62/1.79      inference('simplify', [status(thm)], ['26'])).
% 1.62/1.79  thf('28', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.62/1.79          (k2_zfmisc_1 @ X2 @ X0))),
% 1.62/1.79      inference('sup+', [status(thm)], ['20', '27'])).
% 1.62/1.79  thf('29', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (r1_tarski @ 
% 1.62/1.79          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.62/1.79           (k3_xboole_0 @ X0 @ sk_B)) @ 
% 1.62/1.79          (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['19', '28'])).
% 1.62/1.79  thf('30', plain,
% 1.62/1.79      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X21))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 1.62/1.79              (k2_zfmisc_1 @ X20 @ X21)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.62/1.79  thf('31', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('32', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['8', '9'])).
% 1.62/1.79  thf('33', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_D_1)) @ 
% 1.62/1.79          (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 1.62/1.79  thf('34', plain,
% 1.62/1.79      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79        (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['18', '33'])).
% 1.62/1.79  thf('35', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.62/1.79      inference('demod', [status(thm)], ['17', '34'])).
% 1.62/1.79  thf('36', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.62/1.79      inference('simplify', [status(thm)], ['26'])).
% 1.62/1.79  thf('37', plain,
% 1.62/1.79      (![X10 : $i, X12 : $i]:
% 1.62/1.79         (((X10) = (X12))
% 1.62/1.79          | ~ (r1_tarski @ X12 @ X10)
% 1.62/1.79          | ~ (r1_tarski @ X10 @ X12))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('38', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]:
% 1.62/1.79         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.62/1.79          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['36', '37'])).
% 1.62/1.79  thf('39', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.62/1.79      inference('sup-', [status(thm)], ['35', '38'])).
% 1.62/1.79  thf('40', plain,
% 1.62/1.79      (![X1 : $i, X3 : $i]:
% 1.62/1.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.62/1.79      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.79  thf('41', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.62/1.79         (~ (r2_hidden @ X8 @ X7)
% 1.62/1.79          | (r2_hidden @ X8 @ X5)
% 1.62/1.79          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.62/1.79      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.62/1.79  thf('42', plain,
% 1.62/1.79      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.62/1.79         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.62/1.79      inference('simplify', [status(thm)], ['41'])).
% 1.62/1.79  thf('43', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.62/1.79          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.62/1.79      inference('sup-', [status(thm)], ['40', '42'])).
% 1.62/1.79  thf('44', plain,
% 1.62/1.79      (![X1 : $i, X3 : $i]:
% 1.62/1.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.62/1.79      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.79  thf('45', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]:
% 1.62/1.79         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.62/1.79          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['43', '44'])).
% 1.62/1.79  thf('46', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.62/1.79      inference('simplify', [status(thm)], ['45'])).
% 1.62/1.79  thf('47', plain,
% 1.62/1.79      (![X10 : $i, X12 : $i]:
% 1.62/1.79         (((X10) = (X12))
% 1.62/1.79          | ~ (r1_tarski @ X12 @ X10)
% 1.62/1.79          | ~ (r1_tarski @ X10 @ X12))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('48', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]:
% 1.62/1.79         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.62/1.79          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['46', '47'])).
% 1.62/1.79  thf('49', plain,
% 1.62/1.79      ((~ (r1_tarski @ sk_C_1 @ sk_A)
% 1.62/1.79        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['39', '48'])).
% 1.62/1.79  thf('50', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.62/1.79      inference('sup-', [status(thm)], ['35', '38'])).
% 1.62/1.79  thf('51', plain, ((~ (r1_tarski @ sk_C_1 @ sk_A) | ((sk_C_1) = (sk_A)))),
% 1.62/1.79      inference('demod', [status(thm)], ['49', '50'])).
% 1.62/1.79  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.62/1.79      inference('sup-', [status(thm)], ['2', '3'])).
% 1.62/1.79  thf('53', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('54', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['8', '9'])).
% 1.62/1.79  thf('55', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79              (k2_zfmisc_1 @ sk_A @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['53', '54'])).
% 1.62/1.79  thf('56', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['4', '5'])).
% 1.62/1.79  thf('57', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1)
% 1.62/1.79         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['55', '56'])).
% 1.62/1.79  thf('58', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.62/1.79      inference('sup-', [status(thm)], ['35', '38'])).
% 1.62/1.79  thf('59', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_D_1)
% 1.62/1.79         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('demod', [status(thm)], ['57', '58'])).
% 1.62/1.79  thf('60', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['4', '5'])).
% 1.62/1.79  thf('61', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.62/1.79      inference('simplify', [status(thm)], ['45'])).
% 1.62/1.79  thf('62', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 1.62/1.79          (k2_zfmisc_1 @ X2 @ X0))),
% 1.62/1.79      inference('sup+', [status(thm)], ['60', '61'])).
% 1.62/1.79  thf('63', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (r1_tarski @ 
% 1.62/1.79          (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 1.62/1.79           (k3_xboole_0 @ sk_B @ sk_D_1)) @ 
% 1.62/1.79          (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 1.62/1.79      inference('sup+', [status(thm)], ['59', '62'])).
% 1.62/1.79  thf('64', plain,
% 1.62/1.79      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X21))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 1.62/1.79              (k2_zfmisc_1 @ X20 @ X21)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.62/1.79  thf('65', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('66', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['4', '5'])).
% 1.62/1.79  thf('67', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1) @ 
% 1.62/1.79          (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 1.62/1.79      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 1.62/1.79  thf('68', plain,
% 1.62/1.79      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79        (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 1.62/1.79      inference('sup+', [status(thm)], ['52', '67'])).
% 1.62/1.79  thf('69', plain,
% 1.62/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.62/1.79         (((X15) = (k1_xboole_0))
% 1.62/1.79          | (r1_tarski @ X16 @ X17)
% 1.62/1.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 1.62/1.79               (k2_zfmisc_1 @ X17 @ X15)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.62/1.79  thf('70', plain,
% 1.62/1.79      (((r1_tarski @ sk_C_1 @ sk_A) | ((sk_D_1) = (k1_xboole_0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['68', '69'])).
% 1.62/1.79  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('72', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_D_1)
% 1.62/1.79         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 1.62/1.79      inference('demod', [status(thm)], ['57', '58'])).
% 1.62/1.79  thf('73', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.62/1.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79              (k2_zfmisc_1 @ sk_A @ X0)))),
% 1.62/1.79      inference('sup+', [status(thm)], ['53', '54'])).
% 1.62/1.79  thf('74', plain,
% 1.62/1.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.62/1.79      inference('simplify', [status(thm)], ['45'])).
% 1.62/1.79  thf('75', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 1.62/1.79          (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('sup+', [status(thm)], ['73', '74'])).
% 1.62/1.79  thf('76', plain,
% 1.62/1.79      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 1.62/1.79        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('sup+', [status(thm)], ['72', '75'])).
% 1.62/1.79  thf('77', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('78', plain,
% 1.62/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.62/1.79         (((X15) = (k1_xboole_0))
% 1.62/1.79          | (r1_tarski @ X16 @ X17)
% 1.62/1.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 1.62/1.79               (k2_zfmisc_1 @ X15 @ X17)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.62/1.79  thf('79', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.62/1.79             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 1.62/1.79          | (r1_tarski @ X0 @ sk_B)
% 1.62/1.79          | ((sk_A) = (k1_xboole_0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['77', '78'])).
% 1.62/1.79  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('81', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.62/1.79             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 1.62/1.79          | (r1_tarski @ X0 @ sk_B))),
% 1.62/1.79      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 1.62/1.79  thf('82', plain, ((r1_tarski @ sk_D_1 @ sk_B)),
% 1.62/1.79      inference('sup-', [status(thm)], ['76', '81'])).
% 1.62/1.79  thf('83', plain,
% 1.62/1.79      (![X10 : $i, X12 : $i]:
% 1.62/1.79         (((X10) = (X12))
% 1.62/1.79          | ~ (r1_tarski @ X12 @ X10)
% 1.62/1.79          | ~ (r1_tarski @ X10 @ X12))),
% 1.62/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.62/1.79  thf('84', plain, ((~ (r1_tarski @ sk_B @ sk_D_1) | ((sk_B) = (sk_D_1)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['82', '83'])).
% 1.62/1.79  thf('85', plain,
% 1.62/1.79      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79        (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 1.62/1.79      inference('sup+', [status(thm)], ['52', '67'])).
% 1.62/1.79  thf('86', plain,
% 1.62/1.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('87', plain,
% 1.62/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.62/1.79         (((X15) = (k1_xboole_0))
% 1.62/1.79          | (r1_tarski @ X16 @ X17)
% 1.62/1.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 1.62/1.79               (k2_zfmisc_1 @ X15 @ X17)))),
% 1.62/1.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.62/1.79  thf('88', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79             (k2_zfmisc_1 @ sk_A @ X0))
% 1.62/1.79          | (r1_tarski @ sk_B @ X0)
% 1.62/1.79          | ((sk_A) = (k1_xboole_0)))),
% 1.62/1.79      inference('sup-', [status(thm)], ['86', '87'])).
% 1.62/1.79  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('90', plain,
% 1.62/1.79      (![X0 : $i]:
% 1.62/1.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.62/1.79             (k2_zfmisc_1 @ sk_A @ X0))
% 1.62/1.79          | (r1_tarski @ sk_B @ X0))),
% 1.62/1.79      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.62/1.79  thf('91', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 1.62/1.79      inference('sup-', [status(thm)], ['85', '90'])).
% 1.62/1.79  thf('92', plain, (((sk_B) = (sk_D_1))),
% 1.62/1.79      inference('demod', [status(thm)], ['84', '91'])).
% 1.62/1.79  thf('93', plain, (((sk_D_1) != (k1_xboole_0))),
% 1.62/1.79      inference('demod', [status(thm)], ['71', '92'])).
% 1.62/1.79  thf('94', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.62/1.79      inference('simplify_reflect-', [status(thm)], ['70', '93'])).
% 1.62/1.79  thf('95', plain, (((sk_C_1) = (sk_A))),
% 1.62/1.79      inference('demod', [status(thm)], ['51', '94'])).
% 1.62/1.79  thf('96', plain, ((((sk_A) != (sk_C_1)) | ((sk_B) != (sk_D_1)))),
% 1.62/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.79  thf('97', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 1.62/1.79      inference('split', [status(esa)], ['96'])).
% 1.62/1.79  thf('98', plain, (((sk_B) = (sk_D_1))),
% 1.62/1.79      inference('demod', [status(thm)], ['84', '91'])).
% 1.62/1.79  thf('99', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 1.62/1.79      inference('split', [status(esa)], ['96'])).
% 1.62/1.79  thf('100', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 1.62/1.79      inference('sup-', [status(thm)], ['98', '99'])).
% 1.62/1.79  thf('101', plain, ((((sk_B) = (sk_D_1)))),
% 1.62/1.79      inference('simplify', [status(thm)], ['100'])).
% 1.62/1.79  thf('102', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B) = (sk_D_1)))),
% 1.62/1.79      inference('split', [status(esa)], ['96'])).
% 1.62/1.79  thf('103', plain, (~ (((sk_A) = (sk_C_1)))),
% 1.62/1.79      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 1.62/1.79  thf('104', plain, (((sk_A) != (sk_C_1))),
% 1.62/1.79      inference('simpl_trail', [status(thm)], ['97', '103'])).
% 1.62/1.79  thf('105', plain, ($false),
% 1.62/1.79      inference('simplify_reflect-', [status(thm)], ['95', '104'])).
% 1.62/1.79  
% 1.62/1.79  % SZS output end Refutation
% 1.62/1.79  
% 1.62/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
