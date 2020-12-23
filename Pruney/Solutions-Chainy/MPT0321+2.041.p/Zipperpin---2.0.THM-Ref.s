%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pVCX0foky

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:38 EST 2020

% Result     : Theorem 9.32s
% Output     : Refutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 976 expanded)
%              Number of leaves         :   26 ( 303 expanded)
%              Depth                    :   31
%              Number of atoms          :  952 (8754 expanded)
%              Number of equality atoms :   76 (1170 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X38 ) )
      | ~ ( r2_hidden @ X36 @ X38 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_1 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_zfmisc_1 @ X40 @ X41 )
        = k1_xboole_0 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X40: $i] :
      ( ( k2_zfmisc_1 @ X40 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X40 @ X39 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','32'])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_3 @ sk_A )
    | ( r1_tarski @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_C_3 @ sk_A ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('38',plain,
    ( ( sk_C_3 = sk_A )
    | ( r2_xboole_0 @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X38 ) )
      | ~ ( r2_hidden @ X36 @ X38 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('50',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_zfmisc_1 @ X40 @ X41 )
        = k1_xboole_0 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X41: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X41 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','51'])).

thf('53',plain,(
    ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28','29'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_1 ) @ sk_B_1 )
      | ( r1_tarski @ sk_D_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B_1 )
    | ( r1_tarski @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_D_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('61',plain,
    ( ( sk_D_1 = sk_B_1 )
    | ( r2_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('63',plain,
    ( ( sk_D_1 = sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_B_1 @ sk_D_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('73',plain,(
    r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_3 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_3 ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ sk_B_1 @ sk_D_1 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_D_1 = sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_B_1 @ sk_D_1 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('86',plain,
    ( ( sk_D_1 = sk_B_1 )
    | ~ ( r2_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_D_1 = sk_B_1 )
    | ( r2_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('88',plain,(
    sk_D_1 = sk_B_1 ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['39','88'])).

thf('90',plain,
    ( ( sk_C_3 = sk_A )
    | ( r2_xboole_0 @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('92',plain,
    ( ( sk_C_3 = sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_C_3 = sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ ( sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( sk_C_3 = sk_A ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    sk_D_1 = sk_B_1 ),
    inference(clc,[status(thm)],['86','87'])).

thf('99',plain,
    ( ( sk_B_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['96'])).

thf('100',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B_1 = sk_D_1 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['96'])).

thf('103',plain,(
    sk_A != sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A != sk_C_3 ),
    inference(simpl_trail,[status(thm)],['97','103'])).

thf('105',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ ( sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['95','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('107',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ ( sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('109',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A @ sk_C_3 ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('111',plain,(
    ~ ( r2_xboole_0 @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_C_3 = sk_A ),
    inference('sup-',[status(thm)],['38','111'])).

thf('113',plain,(
    sk_A != sk_C_3 ),
    inference(simpl_trail,[status(thm)],['97','103'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pVCX0foky
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 9.32/9.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.32/9.58  % Solved by: fo/fo7.sh
% 9.32/9.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.32/9.58  % done 8364 iterations in 9.128s
% 9.32/9.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.32/9.58  % SZS output start Refutation
% 9.32/9.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.32/9.58  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 9.32/9.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.32/9.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.32/9.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.32/9.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.32/9.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 9.32/9.58  thf(sk_C_3_type, type, sk_C_3: $i).
% 9.32/9.58  thf(sk_B_type, type, sk_B: $i > $i).
% 9.32/9.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.32/9.58  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 9.32/9.58  thf(sk_A_type, type, sk_A: $i).
% 9.32/9.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.32/9.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.32/9.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 9.32/9.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.32/9.58  thf(d3_tarski, axiom,
% 9.32/9.58    (![A:$i,B:$i]:
% 9.32/9.58     ( ( r1_tarski @ A @ B ) <=>
% 9.32/9.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.32/9.58  thf('0', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf(d1_xboole_0, axiom,
% 9.32/9.58    (![A:$i]:
% 9.32/9.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 9.32/9.58  thf('1', plain,
% 9.32/9.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 9.32/9.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.32/9.58  thf(l54_zfmisc_1, axiom,
% 9.32/9.58    (![A:$i,B:$i,C:$i,D:$i]:
% 9.32/9.58     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 9.32/9.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 9.32/9.58  thf('2', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 9.32/9.58         ((r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X38))
% 9.32/9.58          | ~ (r2_hidden @ X36 @ X38)
% 9.32/9.58          | ~ (r2_hidden @ X34 @ X35))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('3', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ X0)
% 9.32/9.58          | ~ (r2_hidden @ X2 @ X1)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X1 @ X0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['1', '2'])).
% 9.32/9.58  thf('4', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.32/9.58         ((r1_tarski @ X0 @ X1)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X0 @ X2))
% 9.32/9.58          | (v1_xboole_0 @ X2))),
% 9.32/9.58      inference('sup-', [status(thm)], ['0', '3'])).
% 9.32/9.58  thf(t134_zfmisc_1, conjecture,
% 9.32/9.58    (![A:$i,B:$i,C:$i,D:$i]:
% 9.32/9.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 9.32/9.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.32/9.58         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 9.32/9.58  thf(zf_stmt_0, negated_conjecture,
% 9.32/9.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 9.32/9.58        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 9.32/9.58          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.32/9.58            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 9.32/9.58    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 9.32/9.58  thf('5', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('6', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 9.32/9.58         ((r2_hidden @ X34 @ X35)
% 9.32/9.58          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('7', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 9.32/9.58             (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58          | (r2_hidden @ X1 @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['5', '6'])).
% 9.32/9.58  thf('8', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ sk_D_1)
% 9.32/9.58          | (r1_tarski @ sk_C_3 @ X0)
% 9.32/9.58          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['4', '7'])).
% 9.32/9.58  thf('9', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf(t2_boole, axiom,
% 9.32/9.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.32/9.58  thf('10', plain,
% 9.32/9.58      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 9.32/9.58      inference('cnf', [status(esa)], [t2_boole])).
% 9.32/9.58  thf(t4_xboole_0, axiom,
% 9.32/9.58    (![A:$i,B:$i]:
% 9.32/9.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 9.32/9.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 9.32/9.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 9.32/9.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 9.32/9.58  thf('11', plain,
% 9.32/9.58      (![X10 : $i, X12 : $i, X13 : $i]:
% 9.32/9.58         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 9.32/9.58          | ~ (r1_xboole_0 @ X10 @ X13))),
% 9.32/9.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 9.32/9.58  thf('12', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['10', '11'])).
% 9.32/9.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 9.32/9.58  thf('13', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 9.32/9.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 9.32/9.58  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 9.32/9.58      inference('demod', [status(thm)], ['12', '13'])).
% 9.32/9.58  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 9.32/9.58      inference('sup-', [status(thm)], ['9', '14'])).
% 9.32/9.58  thf(d8_xboole_0, axiom,
% 9.32/9.58    (![A:$i,B:$i]:
% 9.32/9.58     ( ( r2_xboole_0 @ A @ B ) <=>
% 9.32/9.58       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 9.32/9.58  thf('16', plain,
% 9.32/9.58      (![X7 : $i, X9 : $i]:
% 9.32/9.58         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 9.32/9.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 9.32/9.58  thf('17', plain,
% 9.32/9.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['15', '16'])).
% 9.32/9.58  thf(t6_xboole_0, axiom,
% 9.32/9.58    (![A:$i,B:$i]:
% 9.32/9.58     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 9.32/9.58          ( ![C:$i]:
% 9.32/9.58            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 9.32/9.58  thf('18', plain,
% 9.32/9.58      (![X14 : $i, X15 : $i]:
% 9.32/9.58         (~ (r2_xboole_0 @ X14 @ X15)
% 9.32/9.58          | (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X15))),
% 9.32/9.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 9.32/9.58  thf('19', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         (((k1_xboole_0) = (X0))
% 9.32/9.58          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['17', '18'])).
% 9.32/9.58  thf('20', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 9.32/9.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.32/9.58  thf('21', plain,
% 9.32/9.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['19', '20'])).
% 9.32/9.58  thf(t113_zfmisc_1, axiom,
% 9.32/9.58    (![A:$i,B:$i]:
% 9.32/9.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.32/9.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.32/9.58  thf('22', plain,
% 9.32/9.58      (![X40 : $i, X41 : $i]:
% 9.32/9.58         (((k2_zfmisc_1 @ X40 @ X41) = (k1_xboole_0))
% 9.32/9.58          | ((X41) != (k1_xboole_0)))),
% 9.32/9.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.32/9.58  thf('23', plain,
% 9.32/9.58      (![X40 : $i]: ((k2_zfmisc_1 @ X40 @ k1_xboole_0) = (k1_xboole_0))),
% 9.32/9.58      inference('simplify', [status(thm)], ['22'])).
% 9.32/9.58  thf('24', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup+', [status(thm)], ['21', '23'])).
% 9.32/9.58  thf('25', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('26', plain,
% 9.32/9.58      (![X39 : $i, X40 : $i]:
% 9.32/9.58         (((X39) = (k1_xboole_0))
% 9.32/9.58          | ((X40) = (k1_xboole_0))
% 9.32/9.58          | ((k2_zfmisc_1 @ X40 @ X39) != (k1_xboole_0)))),
% 9.32/9.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.32/9.58  thf('27', plain,
% 9.32/9.58      ((((k2_zfmisc_1 @ sk_C_3 @ sk_D_1) != (k1_xboole_0))
% 9.32/9.58        | ((sk_A) = (k1_xboole_0))
% 9.32/9.58        | ((sk_B_1) = (k1_xboole_0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['25', '26'])).
% 9.32/9.58  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('30', plain, (((k2_zfmisc_1 @ sk_C_3 @ sk_D_1) != (k1_xboole_0))),
% 9.32/9.58      inference('simplify_reflect-', [status(thm)], ['27', '28', '29'])).
% 9.32/9.58  thf('31', plain,
% 9.32/9.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_D_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['24', '30'])).
% 9.32/9.58  thf('32', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 9.32/9.58      inference('simplify', [status(thm)], ['31'])).
% 9.32/9.58  thf('33', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_A) | (r1_tarski @ sk_C_3 @ X0))),
% 9.32/9.58      inference('clc', [status(thm)], ['8', '32'])).
% 9.32/9.58  thf('34', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf('35', plain,
% 9.32/9.58      (((r1_tarski @ sk_C_3 @ sk_A) | (r1_tarski @ sk_C_3 @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['33', '34'])).
% 9.32/9.58  thf('36', plain, ((r1_tarski @ sk_C_3 @ sk_A)),
% 9.32/9.58      inference('simplify', [status(thm)], ['35'])).
% 9.32/9.58  thf('37', plain,
% 9.32/9.58      (![X7 : $i, X9 : $i]:
% 9.32/9.58         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 9.32/9.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 9.32/9.58  thf('38', plain, ((((sk_C_3) = (sk_A)) | (r2_xboole_0 @ sk_C_3 @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['36', '37'])).
% 9.32/9.58  thf('39', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('40', plain,
% 9.32/9.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 9.32/9.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.32/9.58  thf('41', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf('42', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 9.32/9.58         ((r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X38))
% 9.32/9.58          | ~ (r2_hidden @ X36 @ X38)
% 9.32/9.58          | ~ (r2_hidden @ X34 @ X35))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('43', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.32/9.58         ((r1_tarski @ X0 @ X1)
% 9.32/9.58          | ~ (r2_hidden @ X3 @ X2)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X2 @ X0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['41', '42'])).
% 9.32/9.58  thf('44', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ X0)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X0 @ X1))
% 9.32/9.58          | (r1_tarski @ X1 @ X2))),
% 9.32/9.58      inference('sup-', [status(thm)], ['40', '43'])).
% 9.32/9.58  thf('45', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('46', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 9.32/9.58         ((r2_hidden @ X36 @ X37)
% 9.32/9.58          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('47', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 9.32/9.58             (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58          | (r2_hidden @ X0 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['45', '46'])).
% 9.32/9.58  thf('48', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((r1_tarski @ sk_D_1 @ X0)
% 9.32/9.58          | (v1_xboole_0 @ sk_C_3)
% 9.32/9.58          | (r2_hidden @ (sk_C @ X0 @ sk_D_1) @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['44', '47'])).
% 9.32/9.58  thf('49', plain,
% 9.32/9.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['19', '20'])).
% 9.32/9.58  thf('50', plain,
% 9.32/9.58      (![X40 : $i, X41 : $i]:
% 9.32/9.58         (((k2_zfmisc_1 @ X40 @ X41) = (k1_xboole_0))
% 9.32/9.58          | ((X40) != (k1_xboole_0)))),
% 9.32/9.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.32/9.58  thf('51', plain,
% 9.32/9.58      (![X41 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X41) = (k1_xboole_0))),
% 9.32/9.58      inference('simplify', [status(thm)], ['50'])).
% 9.32/9.58  thf('52', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup+', [status(thm)], ['49', '51'])).
% 9.32/9.58  thf('53', plain, (((k2_zfmisc_1 @ sk_C_3 @ sk_D_1) != (k1_xboole_0))),
% 9.32/9.58      inference('simplify_reflect-', [status(thm)], ['27', '28', '29'])).
% 9.32/9.58  thf('54', plain,
% 9.32/9.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_3))),
% 9.32/9.58      inference('sup-', [status(thm)], ['52', '53'])).
% 9.32/9.58  thf('55', plain, (~ (v1_xboole_0 @ sk_C_3)),
% 9.32/9.58      inference('simplify', [status(thm)], ['54'])).
% 9.32/9.58  thf('56', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((r2_hidden @ (sk_C @ X0 @ sk_D_1) @ sk_B_1)
% 9.32/9.58          | (r1_tarski @ sk_D_1 @ X0))),
% 9.32/9.58      inference('clc', [status(thm)], ['48', '55'])).
% 9.32/9.58  thf('57', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf('58', plain,
% 9.32/9.58      (((r1_tarski @ sk_D_1 @ sk_B_1) | (r1_tarski @ sk_D_1 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['56', '57'])).
% 9.32/9.58  thf('59', plain, ((r1_tarski @ sk_D_1 @ sk_B_1)),
% 9.32/9.58      inference('simplify', [status(thm)], ['58'])).
% 9.32/9.58  thf('60', plain,
% 9.32/9.58      (![X7 : $i, X9 : $i]:
% 9.32/9.58         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 9.32/9.58      inference('cnf', [status(esa)], [d8_xboole_0])).
% 9.32/9.58  thf('61', plain, ((((sk_D_1) = (sk_B_1)) | (r2_xboole_0 @ sk_D_1 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['59', '60'])).
% 9.32/9.58  thf('62', plain,
% 9.32/9.58      (![X14 : $i, X15 : $i]:
% 9.32/9.58         (~ (r2_xboole_0 @ X14 @ X15)
% 9.32/9.58          | (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X15))),
% 9.32/9.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 9.32/9.58  thf('63', plain,
% 9.32/9.58      ((((sk_D_1) = (sk_B_1))
% 9.32/9.58        | (r2_hidden @ (sk_C_2 @ sk_B_1 @ sk_D_1) @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['61', '62'])).
% 9.32/9.58  thf('64', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('65', plain,
% 9.32/9.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 9.32/9.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.32/9.58  thf('66', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ X0)
% 9.32/9.58          | ~ (r2_hidden @ X2 @ X1)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X1 @ X0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['1', '2'])).
% 9.32/9.58  thf('67', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ X0)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X0 @ X1))
% 9.32/9.58          | (v1_xboole_0 @ X1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['65', '66'])).
% 9.32/9.58  thf('68', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 9.32/9.58             (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58          | (r2_hidden @ X1 @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['5', '6'])).
% 9.32/9.58  thf('69', plain,
% 9.32/9.58      (((v1_xboole_0 @ sk_D_1)
% 9.32/9.58        | (v1_xboole_0 @ sk_C_3)
% 9.32/9.58        | (r2_hidden @ (sk_B @ sk_C_3) @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['67', '68'])).
% 9.32/9.58  thf('70', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 9.32/9.58      inference('simplify', [status(thm)], ['31'])).
% 9.32/9.58  thf('71', plain,
% 9.32/9.58      (((r2_hidden @ (sk_B @ sk_C_3) @ sk_A) | (v1_xboole_0 @ sk_C_3))),
% 9.32/9.58      inference('clc', [status(thm)], ['69', '70'])).
% 9.32/9.58  thf('72', plain, (~ (v1_xboole_0 @ sk_C_3)),
% 9.32/9.58      inference('simplify', [status(thm)], ['54'])).
% 9.32/9.58  thf('73', plain, ((r2_hidden @ (sk_B @ sk_C_3) @ sk_A)),
% 9.32/9.58      inference('clc', [status(thm)], ['71', '72'])).
% 9.32/9.58  thf('74', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.32/9.58         ((r1_tarski @ X0 @ X1)
% 9.32/9.58          | ~ (r2_hidden @ X3 @ X2)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X2 @ X0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['41', '42'])).
% 9.32/9.58  thf('75', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i]:
% 9.32/9.58         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_C_3) @ (sk_C @ X1 @ X0)) @ 
% 9.32/9.58           (k2_zfmisc_1 @ sk_A @ X0))
% 9.32/9.58          | (r1_tarski @ X0 @ X1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['73', '74'])).
% 9.32/9.58  thf('76', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_C_3) @ (sk_C @ X0 @ sk_B_1)) @ 
% 9.32/9.58           (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58          | (r1_tarski @ sk_B_1 @ X0))),
% 9.32/9.58      inference('sup+', [status(thm)], ['64', '75'])).
% 9.32/9.58  thf('77', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 9.32/9.58         ((r2_hidden @ X36 @ X37)
% 9.32/9.58          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('78', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         ((r1_tarski @ sk_B_1 @ X0)
% 9.32/9.58          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['76', '77'])).
% 9.32/9.58  thf('79', plain,
% 9.32/9.58      (![X4 : $i, X6 : $i]:
% 9.32/9.58         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf('80', plain,
% 9.32/9.58      (((r1_tarski @ sk_B_1 @ sk_D_1) | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['78', '79'])).
% 9.32/9.58  thf('81', plain, ((r1_tarski @ sk_B_1 @ sk_D_1)),
% 9.32/9.58      inference('simplify', [status(thm)], ['80'])).
% 9.32/9.58  thf('82', plain,
% 9.32/9.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 9.32/9.58         (~ (r2_hidden @ X3 @ X4)
% 9.32/9.58          | (r2_hidden @ X3 @ X5)
% 9.32/9.58          | ~ (r1_tarski @ X4 @ X5))),
% 9.32/9.58      inference('cnf', [status(esa)], [d3_tarski])).
% 9.32/9.58  thf('83', plain,
% 9.32/9.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['81', '82'])).
% 9.32/9.58  thf('84', plain,
% 9.32/9.58      ((((sk_D_1) = (sk_B_1))
% 9.32/9.58        | (r2_hidden @ (sk_C_2 @ sk_B_1 @ sk_D_1) @ sk_D_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['63', '83'])).
% 9.32/9.58  thf('85', plain,
% 9.32/9.58      (![X14 : $i, X15 : $i]:
% 9.32/9.58         (~ (r2_xboole_0 @ X14 @ X15)
% 9.32/9.58          | ~ (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X14))),
% 9.32/9.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 9.32/9.58  thf('86', plain,
% 9.32/9.58      ((((sk_D_1) = (sk_B_1)) | ~ (r2_xboole_0 @ sk_D_1 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['84', '85'])).
% 9.32/9.58  thf('87', plain, ((((sk_D_1) = (sk_B_1)) | (r2_xboole_0 @ sk_D_1 @ sk_B_1))),
% 9.32/9.58      inference('sup-', [status(thm)], ['59', '60'])).
% 9.32/9.58  thf('88', plain, (((sk_D_1) = (sk_B_1))),
% 9.32/9.58      inference('clc', [status(thm)], ['86', '87'])).
% 9.32/9.58  thf('89', plain,
% 9.32/9.58      (((k2_zfmisc_1 @ sk_A @ sk_D_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('demod', [status(thm)], ['39', '88'])).
% 9.32/9.58  thf('90', plain, ((((sk_C_3) = (sk_A)) | (r2_xboole_0 @ sk_C_3 @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['36', '37'])).
% 9.32/9.58  thf('91', plain,
% 9.32/9.58      (![X14 : $i, X15 : $i]:
% 9.32/9.58         (~ (r2_xboole_0 @ X14 @ X15)
% 9.32/9.58          | (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X15))),
% 9.32/9.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 9.32/9.58  thf('92', plain,
% 9.32/9.58      ((((sk_C_3) = (sk_A)) | (r2_hidden @ (sk_C_2 @ sk_A @ sk_C_3) @ sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['90', '91'])).
% 9.32/9.58  thf('93', plain,
% 9.32/9.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.32/9.58         ((v1_xboole_0 @ X0)
% 9.32/9.58          | ~ (r2_hidden @ X2 @ X1)
% 9.32/9.58          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ X1 @ X0)))),
% 9.32/9.58      inference('sup-', [status(thm)], ['1', '2'])).
% 9.32/9.58  thf('94', plain,
% 9.32/9.58      (![X0 : $i]:
% 9.32/9.58         (((sk_C_3) = (sk_A))
% 9.32/9.58          | (r2_hidden @ 
% 9.32/9.58             (k4_tarski @ (sk_C_2 @ sk_A @ sk_C_3) @ (sk_B @ X0)) @ 
% 9.32/9.58             (k2_zfmisc_1 @ sk_A @ X0))
% 9.32/9.58          | (v1_xboole_0 @ X0))),
% 9.32/9.58      inference('sup-', [status(thm)], ['92', '93'])).
% 9.32/9.58  thf('95', plain,
% 9.32/9.58      (((r2_hidden @ 
% 9.32/9.58         (k4_tarski @ (sk_C_2 @ sk_A @ sk_C_3) @ (sk_B @ sk_D_1)) @ 
% 9.32/9.58         (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58        | (v1_xboole_0 @ sk_D_1)
% 9.32/9.58        | ((sk_C_3) = (sk_A)))),
% 9.32/9.58      inference('sup+', [status(thm)], ['89', '94'])).
% 9.32/9.58  thf('96', plain, ((((sk_A) != (sk_C_3)) | ((sk_B_1) != (sk_D_1)))),
% 9.32/9.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.32/9.58  thf('97', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 9.32/9.58      inference('split', [status(esa)], ['96'])).
% 9.32/9.58  thf('98', plain, (((sk_D_1) = (sk_B_1))),
% 9.32/9.58      inference('clc', [status(thm)], ['86', '87'])).
% 9.32/9.58  thf('99', plain, ((((sk_B_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 9.32/9.58      inference('split', [status(esa)], ['96'])).
% 9.32/9.58  thf('100', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 9.32/9.58      inference('sup-', [status(thm)], ['98', '99'])).
% 9.32/9.58  thf('101', plain, ((((sk_B_1) = (sk_D_1)))),
% 9.32/9.58      inference('simplify', [status(thm)], ['100'])).
% 9.32/9.58  thf('102', plain, (~ (((sk_A) = (sk_C_3))) | ~ (((sk_B_1) = (sk_D_1)))),
% 9.32/9.58      inference('split', [status(esa)], ['96'])).
% 9.32/9.58  thf('103', plain, (~ (((sk_A) = (sk_C_3)))),
% 9.32/9.58      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 9.32/9.58  thf('104', plain, (((sk_A) != (sk_C_3))),
% 9.32/9.58      inference('simpl_trail', [status(thm)], ['97', '103'])).
% 9.32/9.58  thf('105', plain,
% 9.32/9.58      (((r2_hidden @ 
% 9.32/9.58         (k4_tarski @ (sk_C_2 @ sk_A @ sk_C_3) @ (sk_B @ sk_D_1)) @ 
% 9.32/9.58         (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))
% 9.32/9.58        | (v1_xboole_0 @ sk_D_1))),
% 9.32/9.58      inference('simplify_reflect-', [status(thm)], ['95', '104'])).
% 9.32/9.58  thf('106', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 9.32/9.58      inference('simplify', [status(thm)], ['31'])).
% 9.32/9.58  thf('107', plain,
% 9.32/9.58      ((r2_hidden @ (k4_tarski @ (sk_C_2 @ sk_A @ sk_C_3) @ (sk_B @ sk_D_1)) @ 
% 9.32/9.58        (k2_zfmisc_1 @ sk_C_3 @ sk_D_1))),
% 9.32/9.58      inference('clc', [status(thm)], ['105', '106'])).
% 9.32/9.58  thf('108', plain,
% 9.32/9.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 9.32/9.58         ((r2_hidden @ X34 @ X35)
% 9.32/9.58          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 9.32/9.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 9.32/9.58  thf('109', plain, ((r2_hidden @ (sk_C_2 @ sk_A @ sk_C_3) @ sk_C_3)),
% 9.32/9.58      inference('sup-', [status(thm)], ['107', '108'])).
% 9.32/9.58  thf('110', plain,
% 9.32/9.58      (![X14 : $i, X15 : $i]:
% 9.32/9.58         (~ (r2_xboole_0 @ X14 @ X15)
% 9.32/9.58          | ~ (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X14))),
% 9.32/9.58      inference('cnf', [status(esa)], [t6_xboole_0])).
% 9.32/9.58  thf('111', plain, (~ (r2_xboole_0 @ sk_C_3 @ sk_A)),
% 9.32/9.58      inference('sup-', [status(thm)], ['109', '110'])).
% 9.32/9.58  thf('112', plain, (((sk_C_3) = (sk_A))),
% 9.32/9.58      inference('sup-', [status(thm)], ['38', '111'])).
% 9.32/9.58  thf('113', plain, (((sk_A) != (sk_C_3))),
% 9.32/9.58      inference('simpl_trail', [status(thm)], ['97', '103'])).
% 9.32/9.58  thf('114', plain, ($false),
% 9.32/9.58      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 9.32/9.58  
% 9.32/9.58  % SZS output end Refutation
% 9.32/9.58  
% 9.32/9.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
