%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gstvZ50W4I

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:56 EST 2020

% Result     : Theorem 6.15s
% Output     : Refutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 218 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  600 (1779 expanded)
%              Number of equality atoms :   31 (  94 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ ( k1_tarski @ X47 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','19'])).

thf(t103_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ D @ A )
          & ! [E: $i,F: $i] :
              ~ ( ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C )
                & ( D
                  = ( k4_tarski @ E @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 )
      | ( r1_xboole_0 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 )
      | ( r1_xboole_0 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('32',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X50 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_2 @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','34'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X43 @ X40 @ X41 ) @ ( sk_E_1 @ X43 @ X40 @ X41 ) @ X43 @ X40 @ X41 )
      | ( X42
       != ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X40: $i,X41: $i,X43: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X43 @ X40 @ X41 ) @ ( sk_E_1 @ X43 @ X40 @ X41 ) @ X43 @ X40 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X33
        = ( k4_tarski @ X31 @ X32 ) )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( sk_D_2
    = ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['35','37'])).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X31 @ X35 )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X53 @ sk_B )
      | ( sk_D_2
       != ( k4_tarski @ X53 @ X54 ) )
      | ~ ( r2_hidden @ X54 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( sk_D_2
       != ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['35','37'])).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ X34 )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_D_2 != sk_D_2 ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gstvZ50W4I
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.15/6.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.15/6.34  % Solved by: fo/fo7.sh
% 6.15/6.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.15/6.34  % done 13533 iterations in 5.886s
% 6.15/6.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.15/6.34  % SZS output start Refutation
% 6.15/6.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.15/6.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.15/6.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.15/6.34  thf(sk_C_type, type, sk_C: $i).
% 6.15/6.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 6.15/6.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.15/6.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.15/6.34  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 6.15/6.34  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.15/6.34  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 6.15/6.34  thf(sk_D_2_type, type, sk_D_2: $i).
% 6.15/6.34  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.15/6.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.15/6.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.15/6.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.15/6.34  thf(sk_A_type, type, sk_A: $i).
% 6.15/6.34  thf(sk_B_type, type, sk_B: $i).
% 6.15/6.34  thf(t69_enumset1, axiom,
% 6.15/6.34    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.15/6.34  thf('0', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 6.15/6.34      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.15/6.34  thf(d10_xboole_0, axiom,
% 6.15/6.34    (![A:$i,B:$i]:
% 6.15/6.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.15/6.34  thf('1', plain,
% 6.15/6.34      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 6.15/6.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.15/6.34  thf('2', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 6.15/6.34      inference('simplify', [status(thm)], ['1'])).
% 6.15/6.34  thf(l1_zfmisc_1, axiom,
% 6.15/6.34    (![A:$i,B:$i]:
% 6.15/6.34     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 6.15/6.34  thf('3', plain,
% 6.15/6.34      (![X47 : $i, X48 : $i]:
% 6.15/6.34         ((r2_hidden @ X47 @ X48) | ~ (r1_tarski @ (k1_tarski @ X47) @ X48))),
% 6.15/6.34      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 6.15/6.34  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.15/6.34      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.34  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 6.15/6.34      inference('sup+', [status(thm)], ['0', '4'])).
% 6.15/6.34  thf(d5_xboole_0, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 6.15/6.34       ( ![D:$i]:
% 6.15/6.34         ( ( r2_hidden @ D @ C ) <=>
% 6.15/6.34           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 6.15/6.34  thf('6', plain,
% 6.15/6.34      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 6.15/6.34         (~ (r2_hidden @ X4 @ X5)
% 6.15/6.34          | (r2_hidden @ X4 @ X6)
% 6.15/6.34          | (r2_hidden @ X4 @ X7)
% 6.15/6.34          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 6.15/6.34      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.15/6.34  thf('7', plain,
% 6.15/6.34      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.15/6.34         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 6.15/6.34          | (r2_hidden @ X4 @ X6)
% 6.15/6.34          | ~ (r2_hidden @ X4 @ X5))),
% 6.15/6.34      inference('simplify', [status(thm)], ['6'])).
% 6.15/6.34  thf('8', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]:
% 6.15/6.34         ((r2_hidden @ X0 @ X1)
% 6.15/6.34          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['5', '7'])).
% 6.15/6.34  thf(t40_xboole_1, axiom,
% 6.15/6.34    (![A:$i,B:$i]:
% 6.15/6.34     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.15/6.34  thf('9', plain,
% 6.15/6.34      (![X23 : $i, X24 : $i]:
% 6.15/6.34         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 6.15/6.34           = (k4_xboole_0 @ X23 @ X24))),
% 6.15/6.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 6.15/6.34  thf(t48_xboole_1, axiom,
% 6.15/6.34    (![A:$i,B:$i]:
% 6.15/6.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.15/6.34  thf('10', plain,
% 6.15/6.34      (![X25 : $i, X26 : $i]:
% 6.15/6.34         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 6.15/6.34           = (k3_xboole_0 @ X25 @ X26))),
% 6.15/6.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.15/6.34  thf('11', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 6.15/6.34      inference('simplify', [status(thm)], ['1'])).
% 6.15/6.34  thf(t106_xboole_1, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.15/6.34       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.15/6.34  thf('12', plain,
% 6.15/6.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.15/6.34         ((r1_xboole_0 @ X13 @ X15)
% 6.15/6.34          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 6.15/6.34      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.15/6.34  thf('13', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 6.15/6.34      inference('sup-', [status(thm)], ['11', '12'])).
% 6.15/6.34  thf('14', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]:
% 6.15/6.34         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 6.15/6.34      inference('sup+', [status(thm)], ['10', '13'])).
% 6.15/6.34  thf('15', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]:
% 6.15/6.34         (r1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 6.15/6.34          (k4_xboole_0 @ X1 @ X0))),
% 6.15/6.34      inference('sup+', [status(thm)], ['9', '14'])).
% 6.15/6.34  thf(commutativity_k3_xboole_0, axiom,
% 6.15/6.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.15/6.34  thf('16', plain,
% 6.15/6.34      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.15/6.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.15/6.34  thf(commutativity_k2_xboole_0, axiom,
% 6.15/6.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.15/6.34  thf('17', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.15/6.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.15/6.34  thf(t21_xboole_1, axiom,
% 6.15/6.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 6.15/6.34  thf('18', plain,
% 6.15/6.34      (![X16 : $i, X17 : $i]:
% 6.15/6.34         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (X16))),
% 6.15/6.34      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.15/6.34  thf('19', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]:
% 6.15/6.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 6.15/6.34      inference('sup+', [status(thm)], ['17', '18'])).
% 6.15/6.34  thf('20', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 6.15/6.34      inference('demod', [status(thm)], ['15', '16', '19'])).
% 6.15/6.34  thf(t103_zfmisc_1, conjecture,
% 6.15/6.34    (![A:$i,B:$i,C:$i,D:$i]:
% 6.15/6.34     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 6.15/6.34          ( r2_hidden @ D @ A ) & 
% 6.15/6.34          ( ![E:$i,F:$i]:
% 6.15/6.34            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 6.15/6.34                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 6.15/6.34  thf(zf_stmt_0, negated_conjecture,
% 6.15/6.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.15/6.34        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 6.15/6.34             ( r2_hidden @ D @ A ) & 
% 6.15/6.34             ( ![E:$i,F:$i]:
% 6.15/6.34               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 6.15/6.34                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 6.15/6.34    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 6.15/6.34  thf('21', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.34  thf(t63_xboole_1, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 6.15/6.34       ( r1_xboole_0 @ A @ C ) ))).
% 6.15/6.34  thf('22', plain,
% 6.15/6.34      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.15/6.34         (~ (r1_tarski @ X27 @ X28)
% 6.15/6.34          | ~ (r1_xboole_0 @ X28 @ X29)
% 6.15/6.34          | (r1_xboole_0 @ X27 @ X29))),
% 6.15/6.34      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.15/6.34  thf('23', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         ((r1_xboole_0 @ sk_A @ X0)
% 6.15/6.34          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ X0))),
% 6.15/6.34      inference('sup-', [status(thm)], ['21', '22'])).
% 6.15/6.34  thf('24', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['20', '23'])).
% 6.15/6.34  thf('25', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.34  thf('26', plain,
% 6.15/6.34      (![X47 : $i, X49 : $i]:
% 6.15/6.34         ((r1_tarski @ (k1_tarski @ X47) @ X49) | ~ (r2_hidden @ X47 @ X49))),
% 6.15/6.34      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 6.15/6.34  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_D_2) @ sk_A)),
% 6.15/6.34      inference('sup-', [status(thm)], ['25', '26'])).
% 6.15/6.34  thf('28', plain,
% 6.15/6.34      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.15/6.34         (~ (r1_tarski @ X27 @ X28)
% 6.15/6.34          | ~ (r1_xboole_0 @ X28 @ X29)
% 6.15/6.34          | (r1_xboole_0 @ X27 @ X29))),
% 6.15/6.34      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.15/6.34  thf('29', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         ((r1_xboole_0 @ (k1_tarski @ sk_D_2) @ X0)
% 6.15/6.34          | ~ (r1_xboole_0 @ sk_A @ X0))),
% 6.15/6.34      inference('sup-', [status(thm)], ['27', '28'])).
% 6.15/6.34  thf('30', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         (r1_xboole_0 @ (k1_tarski @ sk_D_2) @ 
% 6.15/6.34          (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['24', '29'])).
% 6.15/6.34  thf('31', plain,
% 6.15/6.34      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 6.15/6.34      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.15/6.34  thf(t55_zfmisc_1, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 6.15/6.34  thf('32', plain,
% 6.15/6.34      (![X50 : $i, X51 : $i, X52 : $i]:
% 6.15/6.34         (~ (r1_xboole_0 @ (k2_tarski @ X50 @ X51) @ X52)
% 6.15/6.34          | ~ (r2_hidden @ X50 @ X52))),
% 6.15/6.34      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 6.15/6.34  thf('33', plain,
% 6.15/6.34      (![X0 : $i, X1 : $i]:
% 6.15/6.34         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 6.15/6.34      inference('sup-', [status(thm)], ['31', '32'])).
% 6.15/6.34  thf('34', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         ~ (r2_hidden @ sk_D_2 @ 
% 6.15/6.34            (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['30', '33'])).
% 6.15/6.34  thf('35', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 6.15/6.34      inference('sup-', [status(thm)], ['8', '34'])).
% 6.15/6.34  thf(d2_zfmisc_1, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 6.15/6.34       ( ![D:$i]:
% 6.15/6.34         ( ( r2_hidden @ D @ C ) <=>
% 6.15/6.34           ( ?[E:$i,F:$i]:
% 6.15/6.34             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 6.15/6.34               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 6.15/6.34  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 6.15/6.34  thf(zf_stmt_2, axiom,
% 6.15/6.34    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 6.15/6.34     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 6.15/6.34       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 6.15/6.34         ( r2_hidden @ E @ A ) ) ))).
% 6.15/6.34  thf(zf_stmt_3, axiom,
% 6.15/6.34    (![A:$i,B:$i,C:$i]:
% 6.15/6.34     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 6.15/6.34       ( ![D:$i]:
% 6.15/6.34         ( ( r2_hidden @ D @ C ) <=>
% 6.15/6.34           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 6.15/6.34  thf('36', plain,
% 6.15/6.34      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 6.15/6.34         (~ (r2_hidden @ X43 @ X42)
% 6.15/6.34          | (zip_tseitin_0 @ (sk_F_1 @ X43 @ X40 @ X41) @ 
% 6.15/6.34             (sk_E_1 @ X43 @ X40 @ X41) @ X43 @ X40 @ X41)
% 6.15/6.34          | ((X42) != (k2_zfmisc_1 @ X41 @ X40)))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.15/6.34  thf('37', plain,
% 6.15/6.34      (![X40 : $i, X41 : $i, X43 : $i]:
% 6.15/6.34         ((zip_tseitin_0 @ (sk_F_1 @ X43 @ X40 @ X41) @ 
% 6.15/6.34           (sk_E_1 @ X43 @ X40 @ X41) @ X43 @ X40 @ X41)
% 6.15/6.34          | ~ (r2_hidden @ X43 @ (k2_zfmisc_1 @ X41 @ X40)))),
% 6.15/6.34      inference('simplify', [status(thm)], ['36'])).
% 6.15/6.34  thf('38', plain,
% 6.15/6.34      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 6.15/6.34        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 6.15/6.34      inference('sup-', [status(thm)], ['35', '37'])).
% 6.15/6.34  thf('39', plain,
% 6.15/6.34      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.15/6.34         (((X33) = (k4_tarski @ X31 @ X32))
% 6.15/6.34          | ~ (zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.15/6.34  thf('40', plain,
% 6.15/6.34      (((sk_D_2)
% 6.15/6.34         = (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 6.15/6.34            (sk_F_1 @ sk_D_2 @ sk_C @ sk_B)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['38', '39'])).
% 6.15/6.34  thf('41', plain,
% 6.15/6.34      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 6.15/6.34        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 6.15/6.34      inference('sup-', [status(thm)], ['35', '37'])).
% 6.15/6.34  thf('42', plain,
% 6.15/6.34      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.15/6.34         ((r2_hidden @ X31 @ X35)
% 6.15/6.34          | ~ (zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.15/6.34  thf('43', plain, ((r2_hidden @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 6.15/6.34      inference('sup-', [status(thm)], ['41', '42'])).
% 6.15/6.34  thf('44', plain,
% 6.15/6.34      (![X53 : $i, X54 : $i]:
% 6.15/6.34         (~ (r2_hidden @ X53 @ sk_B)
% 6.15/6.34          | ((sk_D_2) != (k4_tarski @ X53 @ X54))
% 6.15/6.34          | ~ (r2_hidden @ X54 @ sk_C))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.34  thf('45', plain,
% 6.15/6.34      (![X0 : $i]:
% 6.15/6.34         (~ (r2_hidden @ X0 @ sk_C)
% 6.15/6.34          | ((sk_D_2) != (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ X0)))),
% 6.15/6.34      inference('sup-', [status(thm)], ['43', '44'])).
% 6.15/6.34  thf('46', plain,
% 6.15/6.34      ((((sk_D_2) != (sk_D_2))
% 6.15/6.34        | ~ (r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_C))),
% 6.15/6.34      inference('sup-', [status(thm)], ['40', '45'])).
% 6.15/6.34  thf('47', plain,
% 6.15/6.34      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 6.15/6.34        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 6.15/6.34      inference('sup-', [status(thm)], ['35', '37'])).
% 6.15/6.34  thf('48', plain,
% 6.15/6.34      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.15/6.34         ((r2_hidden @ X32 @ X34)
% 6.15/6.34          | ~ (zip_tseitin_0 @ X32 @ X31 @ X33 @ X34 @ X35))),
% 6.15/6.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.15/6.34  thf('49', plain, ((r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_C)),
% 6.15/6.34      inference('sup-', [status(thm)], ['47', '48'])).
% 6.15/6.34  thf('50', plain, (((sk_D_2) != (sk_D_2))),
% 6.15/6.34      inference('demod', [status(thm)], ['46', '49'])).
% 6.15/6.34  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 6.15/6.34  
% 6.15/6.34  % SZS output end Refutation
% 6.15/6.34  
% 6.15/6.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
