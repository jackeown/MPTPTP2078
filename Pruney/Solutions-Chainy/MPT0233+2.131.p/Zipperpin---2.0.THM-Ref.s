%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plby08lTcN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:51 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 875 expanded)
%              Number of leaves         :   19 ( 240 expanded)
%              Depth                    :   40
%              Number of atoms          : 1086 (10457 expanded)
%              Number of equality atoms :  207 (1954 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X12 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X12 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X22
        = ( k2_tarski @ X20 @ X21 ) )
      | ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22
        = ( k1_tarski @ X20 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('8',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ( X13 = X12 )
      | ( X13 = X9 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X13 = X9 )
      | ( X13 = X12 )
      | ~ ( r2_hidden @ X13 @ ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D_1 ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X9: $i,X12: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X12 @ X9 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X13 = X9 )
      | ( X13 = X12 )
      | ~ ( r2_hidden @ X13 @ ( k2_tarski @ X12 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('21',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(t9_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D_1 ) )
      | ( sk_D_1 = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( sk_D_1 = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D_1 = sk_B )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X23 ) )
      | ( X22
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('32',plain,(
    ! [X20: $i,X23: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X20 @ X23 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_D_1 = sk_B )
    | ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( sk_D_1 = sk_B )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = sk_B )
      | ( sk_A = sk_B )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference(clc,[status(thm)],['40','44'])).

thf('46',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

thf('47',plain,
    ( ( ( k2_tarski @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_D_1 )
        = ( k1_tarski @ sk_D_1 ) )
      | ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_D_1 )
        = ( k1_tarski @ sk_D_1 ) )
      | ( sk_A = sk_B )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(eq_res,[status(thm)],['50'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('59',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( ( k1_tarski @ X34 )
       != ( k2_tarski @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t9_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D_1 ) )
      | ( sk_A = sk_B )
      | ( sk_A = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D_1 ) )
      | ( sk_A = sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['63'])).

thf('65',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['63'])).

thf('66',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['63'])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','64','65','66'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('68',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X26 )
      | ( X27 = X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( sk_D_1 = X0 )
      | ( sk_D_1 = X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_A )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','69'])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X26 )
      | ( X27 = X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['2','76'])).

thf('78',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_tarski @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('81',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('83',plain,
    ( ( k2_tarski @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X26 )
      | ( X27 = X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( sk_A = X0 )
      | ( sk_A = X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = X0 )
      | ( sk_A = X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(condensation,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plby08lTcN
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.01  % Solved by: fo/fo7.sh
% 0.83/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.01  % done 484 iterations in 0.556s
% 0.83/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.01  % SZS output start Refutation
% 0.83/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.01  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.83/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.01  thf(t28_zfmisc_1, conjecture,
% 0.83/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.01     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.83/1.01          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.83/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.01        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.83/1.01             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.83/1.01    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.83/1.01  thf('0', plain, (((sk_A) != (sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf(d10_xboole_0, axiom,
% 0.83/1.01    (![A:$i,B:$i]:
% 0.83/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.01  thf('1', plain,
% 0.83/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.01  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.01      inference('simplify', [status(thm)], ['1'])).
% 0.83/1.01  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.01      inference('simplify', [status(thm)], ['1'])).
% 0.83/1.01  thf(d2_tarski, axiom,
% 0.83/1.01    (![A:$i,B:$i,C:$i]:
% 0.83/1.01     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.83/1.01       ( ![D:$i]:
% 0.83/1.01         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.83/1.01  thf('4', plain,
% 0.83/1.01      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.01         (((X10) != (X12))
% 0.83/1.01          | (r2_hidden @ X10 @ X11)
% 0.83/1.01          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.83/1.01      inference('cnf', [status(esa)], [d2_tarski])).
% 0.83/1.01  thf('5', plain,
% 0.83/1.01      (![X9 : $i, X12 : $i]: (r2_hidden @ X12 @ (k2_tarski @ X12 @ X9))),
% 0.83/1.01      inference('simplify', [status(thm)], ['4'])).
% 0.83/1.01  thf('6', plain,
% 0.83/1.01      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf(l45_zfmisc_1, axiom,
% 0.83/1.01    (![A:$i,B:$i,C:$i]:
% 0.83/1.01     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.83/1.01       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.83/1.01            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.83/1.01  thf('7', plain,
% 0.83/1.01      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.83/1.01         (((X22) = (k2_tarski @ X20 @ X21))
% 0.83/1.01          | ((X22) = (k1_tarski @ X21))
% 0.83/1.01          | ((X22) = (k1_tarski @ X20))
% 0.83/1.01          | ((X22) = (k1_xboole_0))
% 0.83/1.01          | ~ (r1_tarski @ X22 @ (k2_tarski @ X20 @ X21)))),
% 0.83/1.01      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.83/1.01  thf('8', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.01  thf('9', plain,
% 0.83/1.01      (![X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.01         (~ (r2_hidden @ X13 @ X11)
% 0.83/1.01          | ((X13) = (X12))
% 0.83/1.01          | ((X13) = (X9))
% 0.83/1.01          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.83/1.01      inference('cnf', [status(esa)], [d2_tarski])).
% 0.83/1.01  thf('10', plain,
% 0.83/1.01      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.83/1.01         (((X13) = (X9))
% 0.83/1.01          | ((X13) = (X12))
% 0.83/1.01          | ~ (r2_hidden @ X13 @ (k2_tarski @ X12 @ X9)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['9'])).
% 0.83/1.01  thf('11', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((X0) = (sk_C))
% 0.83/1.01          | ((X0) = (sk_D_1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['8', '10'])).
% 0.83/1.01  thf('12', plain,
% 0.83/1.01      ((((sk_A) = (sk_D_1))
% 0.83/1.01        | ((sk_A) = (sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['5', '11'])).
% 0.83/1.01  thf('13', plain, (((sk_A) != (sk_C))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('14', plain, (((sk_A) != (sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('15', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['12', '13', '14'])).
% 0.83/1.01  thf('16', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.01  thf('17', plain,
% 0.83/1.01      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.01         (((X10) != (X9))
% 0.83/1.01          | (r2_hidden @ X10 @ X11)
% 0.83/1.01          | ((X11) != (k2_tarski @ X12 @ X9)))),
% 0.83/1.01      inference('cnf', [status(esa)], [d2_tarski])).
% 0.83/1.01  thf('18', plain,
% 0.83/1.01      (![X9 : $i, X12 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X12 @ X9))),
% 0.83/1.01      inference('simplify', [status(thm)], ['17'])).
% 0.83/1.01  thf('19', plain,
% 0.83/1.01      (((r2_hidden @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.83/1.01      inference('sup+', [status(thm)], ['16', '18'])).
% 0.83/1.01  thf('20', plain,
% 0.83/1.01      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.83/1.01         (((X13) = (X9))
% 0.83/1.01          | ((X13) = (X12))
% 0.83/1.01          | ~ (r2_hidden @ X13 @ (k2_tarski @ X12 @ X9)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['9'])).
% 0.83/1.01  thf('21', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((sk_D_1) = (sk_A))
% 0.83/1.01        | ((sk_D_1) = (sk_B)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/1.01  thf('22', plain, (((sk_A) != (sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('23', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((sk_D_1) = (sk_B)))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.83/1.01  thf(t9_zfmisc_1, axiom,
% 0.83/1.01    (![A:$i,B:$i,C:$i]:
% 0.83/1.01     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.83/1.01  thf('24', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('25', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_tarski @ sk_D_1))
% 0.83/1.01          | ((sk_D_1) = (sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['23', '24'])).
% 0.83/1.01  thf('26', plain,
% 0.83/1.01      ((((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((sk_D_1) = (sk_B)))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['25'])).
% 0.83/1.01  thf('27', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('28', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_tarski @ sk_C))
% 0.83/1.01          | ((sk_D_1) = (sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.01  thf('29', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((sk_A) = (sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((sk_D_1) = (sk_B))
% 0.83/1.01          | ((k1_tarski @ X0) != (k1_tarski @ sk_C)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['28'])).
% 0.83/1.01  thf('30', plain,
% 0.83/1.01      ((((sk_D_1) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['29'])).
% 0.83/1.01  thf('31', plain,
% 0.83/1.01      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.83/1.01         ((r1_tarski @ X22 @ (k2_tarski @ X20 @ X23))
% 0.83/1.01          | ((X22) != (k1_tarski @ X23)))),
% 0.83/1.01      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.83/1.01  thf('32', plain,
% 0.83/1.01      (![X20 : $i, X23 : $i]:
% 0.83/1.01         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X20 @ X23))),
% 0.83/1.01      inference('simplify', [status(thm)], ['31'])).
% 0.83/1.01  thf('33', plain,
% 0.83/1.01      (((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((sk_D_1) = (sk_B)))),
% 0.83/1.01      inference('sup+', [status(thm)], ['30', '32'])).
% 0.83/1.01  thf(t4_boole, axiom,
% 0.83/1.01    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.83/1.01  thf('34', plain,
% 0.83/1.01      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.83/1.01      inference('cnf', [status(esa)], [t4_boole])).
% 0.83/1.01  thf(l32_xboole_1, axiom,
% 0.83/1.01    (![A:$i,B:$i]:
% 0.83/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.01  thf('35', plain,
% 0.83/1.01      (![X3 : $i, X4 : $i]:
% 0.83/1.01         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.83/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/1.01  thf('36', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.83/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.01  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.83/1.01  thf('38', plain,
% 0.83/1.01      (![X0 : $i, X2 : $i]:
% 0.83/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.01  thf('39', plain,
% 0.83/1.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.83/1.01  thf('40', plain,
% 0.83/1.01      ((((sk_D_1) = (sk_B))
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['33', '39'])).
% 0.83/1.01  thf('41', plain,
% 0.83/1.01      ((((sk_D_1) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['29'])).
% 0.83/1.01  thf('42', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('43', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((sk_D_1) = (sk_B))
% 0.83/1.01          | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['41', '42'])).
% 0.83/1.01  thf('44', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((sk_D_1) = (sk_B))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.83/1.01  thf('45', plain, ((((sk_A) = (sk_B)) | ((sk_D_1) = (sk_B)))),
% 0.83/1.01      inference('clc', [status(thm)], ['40', '44'])).
% 0.83/1.01  thf('46', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['12', '13', '14'])).
% 0.83/1.01  thf('47', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.83/1.01      inference('sup+', [status(thm)], ['45', '46'])).
% 0.83/1.01  thf('48', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('49', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_tarski @ sk_C))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.83/1.01          | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['47', '48'])).
% 0.83/1.01  thf('50', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01          | ((k1_tarski @ X0) != (k1_tarski @ sk_C)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['49'])).
% 0.83/1.01  thf('51', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['50'])).
% 0.83/1.01  thf(t12_zfmisc_1, axiom,
% 0.83/1.01    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.83/1.01  thf('52', plain,
% 0.83/1.01      (![X24 : $i, X25 : $i]:
% 0.83/1.01         (r1_tarski @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))),
% 0.83/1.01      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.83/1.01  thf('53', plain,
% 0.83/1.01      (![X0 : $i, X2 : $i]:
% 0.83/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.01  thf('54', plain,
% 0.83/1.01      (![X0 : $i, X1 : $i]:
% 0.83/1.01         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.83/1.01          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.83/1.01  thf('55', plain,
% 0.83/1.01      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['51', '54'])).
% 0.83/1.01  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.83/1.01  thf('57', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.83/1.01        | ((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.01      inference('demod', [status(thm)], ['55', '56'])).
% 0.83/1.01  thf('58', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('59', plain,
% 0.83/1.01      ((((sk_A) = (sk_B))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('clc', [status(thm)], ['57', '58'])).
% 0.83/1.01  thf('60', plain,
% 0.83/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.01         (((X33) = (X32)) | ((k1_tarski @ X34) != (k2_tarski @ X33 @ X32)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t9_zfmisc_1])).
% 0.83/1.01  thf('61', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_tarski @ sk_D_1))
% 0.83/1.01          | ((sk_A) = (sk_B))
% 0.83/1.01          | ((sk_A) = (sk_D_1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.83/1.01  thf('62', plain, (((sk_A) != (sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('63', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((k1_tarski @ X0) != (k1_tarski @ sk_D_1)) | ((sk_A) = (sk_B)))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.83/1.01  thf('64', plain, (((sk_A) = (sk_B))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['63'])).
% 0.83/1.01  thf('65', plain, (((sk_A) = (sk_B))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['63'])).
% 0.83/1.01  thf('66', plain, (((sk_A) = (sk_B))),
% 0.83/1.01      inference('eq_res', [status(thm)], ['63'])).
% 0.83/1.01  thf('67', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_D_1)))),
% 0.83/1.01      inference('demod', [status(thm)], ['15', '64', '65', '66'])).
% 0.83/1.01  thf(t25_zfmisc_1, axiom,
% 0.83/1.01    (![A:$i,B:$i,C:$i]:
% 0.83/1.01     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.83/1.01          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.83/1.01  thf('68', plain,
% 0.83/1.01      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.83/1.01         (((X27) = (X26))
% 0.83/1.01          | ((X27) = (X28))
% 0.83/1.01          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k2_tarski @ X26 @ X28)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.83/1.01  thf('69', plain,
% 0.83/1.01      (![X0 : $i, X1 : $i]:
% 0.83/1.01         (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k2_tarski @ X1 @ X0))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01          | ((sk_D_1) = (X0))
% 0.83/1.01          | ((sk_D_1) = (X1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.83/1.01  thf('70', plain,
% 0.83/1.01      ((((sk_D_1) = (sk_A))
% 0.83/1.01        | ((sk_D_1) = (sk_A))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['3', '69'])).
% 0.83/1.01  thf('71', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01        | ((sk_D_1) = (sk_A)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['70'])).
% 0.83/1.01  thf('72', plain, (((sk_A) != (sk_D_1))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('73', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_C))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.83/1.01  thf('74', plain,
% 0.83/1.01      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.83/1.01         (((X27) = (X26))
% 0.83/1.01          | ((X27) = (X28))
% 0.83/1.01          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k2_tarski @ X26 @ X28)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.83/1.01  thf('75', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_C))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01          | ((X0) = (sk_A))
% 0.83/1.01          | ((X0) = (sk_A)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['73', '74'])).
% 0.83/1.01  thf('76', plain,
% 0.83/1.01      (![X0 : $i]:
% 0.83/1.01         (((X0) = (sk_A))
% 0.83/1.01          | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.83/1.01          | ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ sk_C)))),
% 0.83/1.01      inference('simplify', [status(thm)], ['75'])).
% 0.83/1.01  thf('77', plain,
% 0.83/1.01      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['2', '76'])).
% 0.83/1.01  thf('78', plain, (((sk_A) != (sk_C))),
% 0.83/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.01  thf('79', plain, (((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.83/1.01  thf('80', plain,
% 0.83/1.01      (![X0 : $i, X1 : $i]:
% 0.83/1.01         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.83/1.01          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['52', '53'])).
% 0.83/1.01  thf('81', plain,
% 0.83/1.01      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.83/1.01        | ((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_A)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['79', '80'])).
% 0.83/1.01  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.83/1.01  thf('83', plain, (((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.83/1.01      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.83/1.01  thf('84', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.83/1.01      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.83/1.01  thf('85', plain,
% 0.83/1.01      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.83/1.01         (((X27) = (X26))
% 0.83/1.01          | ((X27) = (X28))
% 0.83/1.01          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k2_tarski @ X26 @ X28)))),
% 0.83/1.01      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.83/1.01  thf('86', plain,
% 0.83/1.01      (![X0 : $i, X1 : $i]:
% 0.83/1.01         (~ (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.83/1.01          | ((sk_A) = (X0))
% 0.83/1.01          | ((sk_A) = (X1)))),
% 0.83/1.01      inference('sup-', [status(thm)], ['84', '85'])).
% 0.83/1.01  thf('87', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.83/1.01  thf('88', plain, (![X0 : $i, X1 : $i]: (((sk_A) = (X0)) | ((sk_A) = (X1)))),
% 0.83/1.01      inference('demod', [status(thm)], ['86', '87'])).
% 0.83/1.01  thf('89', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.83/1.01      inference('condensation', [status(thm)], ['88'])).
% 0.83/1.01  thf('90', plain, (((sk_A) != (sk_A))),
% 0.83/1.01      inference('demod', [status(thm)], ['0', '89'])).
% 0.83/1.01  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.83/1.01  
% 0.83/1.01  % SZS output end Refutation
% 0.83/1.01  
% 0.83/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
