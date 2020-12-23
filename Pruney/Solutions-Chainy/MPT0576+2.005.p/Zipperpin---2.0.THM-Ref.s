%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z1iVcmyIzY

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:21 EST 2020

% Result     : Theorem 9.61s
% Output     : Refutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 197 expanded)
%              Number of leaves         :   15 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  541 (1645 expanded)
%              Number of equality atoms :   14 (  48 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t180_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t180_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
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
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X14 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_D @ X0 ) @ ( k10_relat_1 @ sk_C @ X0 ) ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k10_relat_1 @ X13 @ X11 ) @ ( k10_relat_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_D @ X1 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_D @ X1 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['12','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('45',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_D @ sk_B ) @ ( k10_relat_1 @ sk_D @ sk_A ) ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_D @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_D @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) )
    = ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X1 ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_D @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z1iVcmyIzY
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 9.61/9.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.61/9.83  % Solved by: fo/fo7.sh
% 9.61/9.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.61/9.83  % done 6622 iterations in 9.389s
% 9.61/9.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.61/9.83  % SZS output start Refutation
% 9.61/9.83  thf(sk_C_type, type, sk_C: $i).
% 9.61/9.83  thf(sk_A_type, type, sk_A: $i).
% 9.61/9.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.61/9.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.61/9.83  thf(sk_D_type, type, sk_D: $i).
% 9.61/9.83  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.61/9.83  thf(sk_B_type, type, sk_B: $i).
% 9.61/9.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.61/9.83  thf(t180_relat_1, conjecture,
% 9.61/9.83    (![A:$i,B:$i,C:$i]:
% 9.61/9.83     ( ( v1_relat_1 @ C ) =>
% 9.61/9.83       ( ![D:$i]:
% 9.61/9.83         ( ( v1_relat_1 @ D ) =>
% 9.61/9.83           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 9.61/9.83             ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ))).
% 9.61/9.83  thf(zf_stmt_0, negated_conjecture,
% 9.61/9.83    (~( ![A:$i,B:$i,C:$i]:
% 9.61/9.83        ( ( v1_relat_1 @ C ) =>
% 9.61/9.83          ( ![D:$i]:
% 9.61/9.84            ( ( v1_relat_1 @ D ) =>
% 9.61/9.84              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 9.61/9.84                ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ) )),
% 9.61/9.84    inference('cnf.neg', [status(esa)], [t180_relat_1])).
% 9.61/9.84  thf('0', plain,
% 9.61/9.84      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf(d10_xboole_0, axiom,
% 9.61/9.84    (![A:$i,B:$i]:
% 9.61/9.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.61/9.84  thf('1', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.61/9.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.61/9.84  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.61/9.84      inference('simplify', [status(thm)], ['1'])).
% 9.61/9.84  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf(t8_xboole_1, axiom,
% 9.61/9.84    (![A:$i,B:$i,C:$i]:
% 9.61/9.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 9.61/9.84       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 9.61/9.84  thf('4', plain,
% 9.61/9.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X8 @ X9)
% 9.61/9.84          | ~ (r1_tarski @ X10 @ X9)
% 9.61/9.84          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.61/9.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.61/9.84  thf('5', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 9.61/9.84          | ~ (r1_tarski @ X0 @ sk_B))),
% 9.61/9.84      inference('sup-', [status(thm)], ['3', '4'])).
% 9.61/9.84  thf('6', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 9.61/9.84      inference('sup-', [status(thm)], ['2', '5'])).
% 9.61/9.84  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.61/9.84      inference('simplify', [status(thm)], ['1'])).
% 9.61/9.84  thf(t10_xboole_1, axiom,
% 9.61/9.84    (![A:$i,B:$i,C:$i]:
% 9.61/9.84     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 9.61/9.84  thf('8', plain,
% 9.61/9.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 9.61/9.84      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.61/9.84  thf('9', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['7', '8'])).
% 9.61/9.84  thf('10', plain,
% 9.61/9.84      (![X0 : $i, X2 : $i]:
% 9.61/9.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.61/9.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.61/9.84  thf('11', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.61/9.84          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['9', '10'])).
% 9.61/9.84  thf('12', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 9.61/9.84      inference('sup-', [status(thm)], ['6', '11'])).
% 9.61/9.84  thf('13', plain, ((r1_tarski @ sk_C @ sk_D)),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf(t179_relat_1, axiom,
% 9.61/9.84    (![A:$i,B:$i]:
% 9.61/9.84     ( ( v1_relat_1 @ B ) =>
% 9.61/9.84       ( ![C:$i]:
% 9.61/9.84         ( ( v1_relat_1 @ C ) =>
% 9.61/9.84           ( ( r1_tarski @ B @ C ) =>
% 9.61/9.84             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 9.61/9.84  thf('14', plain,
% 9.61/9.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 9.61/9.84         (~ (v1_relat_1 @ X14)
% 9.61/9.84          | (r1_tarski @ (k10_relat_1 @ X15 @ X16) @ (k10_relat_1 @ X14 @ X16))
% 9.61/9.84          | ~ (r1_tarski @ X15 @ X14)
% 9.61/9.84          | ~ (v1_relat_1 @ X15))),
% 9.61/9.84      inference('cnf', [status(esa)], [t179_relat_1])).
% 9.61/9.84  thf('15', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         (~ (v1_relat_1 @ sk_C)
% 9.61/9.84          | (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))
% 9.61/9.84          | ~ (v1_relat_1 @ sk_D))),
% 9.61/9.84      inference('sup-', [status(thm)], ['13', '14'])).
% 9.61/9.84  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf('18', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))),
% 9.61/9.84      inference('demod', [status(thm)], ['15', '16', '17'])).
% 9.61/9.84  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.61/9.84      inference('simplify', [status(thm)], ['1'])).
% 9.61/9.84  thf('20', plain,
% 9.61/9.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X8 @ X9)
% 9.61/9.84          | ~ (r1_tarski @ X10 @ X9)
% 9.61/9.84          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.61/9.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.61/9.84  thf('21', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['19', '20'])).
% 9.61/9.84  thf('22', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         (r1_tarski @ 
% 9.61/9.84          (k2_xboole_0 @ (k10_relat_1 @ sk_D @ X0) @ (k10_relat_1 @ sk_C @ X0)) @ 
% 9.61/9.84          (k10_relat_1 @ sk_D @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['18', '21'])).
% 9.61/9.84  thf(t7_xboole_1, axiom,
% 9.61/9.84    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.61/9.84  thf('23', plain,
% 9.61/9.84      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 9.61/9.84      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.61/9.84  thf('24', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['7', '8'])).
% 9.61/9.84  thf('25', plain,
% 9.61/9.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X8 @ X9)
% 9.61/9.84          | ~ (r1_tarski @ X10 @ X9)
% 9.61/9.84          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 9.61/9.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.61/9.84  thf('26', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.61/9.84         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 9.61/9.84          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['24', '25'])).
% 9.61/9.84  thf('27', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['23', '26'])).
% 9.61/9.84  thf('28', plain,
% 9.61/9.84      (![X0 : $i, X2 : $i]:
% 9.61/9.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.61/9.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.61/9.84  thf('29', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 9.61/9.84          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['27', '28'])).
% 9.61/9.84  thf('30', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['23', '26'])).
% 9.61/9.84  thf('31', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.61/9.84      inference('demod', [status(thm)], ['29', '30'])).
% 9.61/9.84  thf('32', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         (r1_tarski @ 
% 9.61/9.84          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0)) @ 
% 9.61/9.84          (k10_relat_1 @ sk_D @ X0))),
% 9.61/9.84      inference('demod', [status(thm)], ['22', '31'])).
% 9.61/9.84  thf('33', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.61/9.84          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['9', '10'])).
% 9.61/9.84  thf('34', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         ((k2_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))
% 9.61/9.84           = (k10_relat_1 @ sk_D @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['32', '33'])).
% 9.61/9.84  thf('35', plain,
% 9.61/9.84      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 9.61/9.84      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.61/9.84  thf(t178_relat_1, axiom,
% 9.61/9.84    (![A:$i,B:$i,C:$i]:
% 9.61/9.84     ( ( v1_relat_1 @ C ) =>
% 9.61/9.84       ( ( r1_tarski @ A @ B ) =>
% 9.61/9.84         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 9.61/9.84  thf('36', plain,
% 9.61/9.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X11 @ X12)
% 9.61/9.84          | ~ (v1_relat_1 @ X13)
% 9.61/9.84          | (r1_tarski @ (k10_relat_1 @ X13 @ X11) @ (k10_relat_1 @ X13 @ X12)))),
% 9.61/9.84      inference('cnf', [status(esa)], [t178_relat_1])).
% 9.61/9.84  thf('37', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.61/9.84         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 9.61/9.84           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.61/9.84          | ~ (v1_relat_1 @ X2))),
% 9.61/9.84      inference('sup-', [status(thm)], ['35', '36'])).
% 9.61/9.84  thf('38', plain,
% 9.61/9.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 9.61/9.84      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.61/9.84  thf('39', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.61/9.84         (~ (v1_relat_1 @ X2)
% 9.61/9.84          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 9.61/9.84             (k2_xboole_0 @ X3 @ (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.61/9.84      inference('sup-', [status(thm)], ['37', '38'])).
% 9.61/9.84  thf('40', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         ((r1_tarski @ (k10_relat_1 @ sk_D @ X1) @ 
% 9.61/9.84           (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))
% 9.61/9.84          | ~ (v1_relat_1 @ sk_D))),
% 9.61/9.84      inference('sup+', [status(thm)], ['34', '39'])).
% 9.61/9.84  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 9.61/9.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.61/9.84  thf('42', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (r1_tarski @ (k10_relat_1 @ sk_D @ X1) @ 
% 9.61/9.84          (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))),
% 9.61/9.84      inference('demod', [status(thm)], ['40', '41'])).
% 9.61/9.84  thf('43', plain,
% 9.61/9.84      ((r1_tarski @ (k10_relat_1 @ sk_D @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('sup+', [status(thm)], ['12', '42'])).
% 9.61/9.84  thf('44', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.61/9.84      inference('sup-', [status(thm)], ['19', '20'])).
% 9.61/9.84  thf('45', plain,
% 9.61/9.84      ((r1_tarski @ 
% 9.61/9.84        (k2_xboole_0 @ (k10_relat_1 @ sk_D @ sk_B) @ 
% 9.61/9.84         (k10_relat_1 @ sk_D @ sk_A)) @ 
% 9.61/9.84        (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('sup-', [status(thm)], ['43', '44'])).
% 9.61/9.84  thf('46', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.61/9.84      inference('demod', [status(thm)], ['29', '30'])).
% 9.61/9.84  thf('47', plain,
% 9.61/9.84      ((r1_tarski @ 
% 9.61/9.84        (k2_xboole_0 @ (k10_relat_1 @ sk_D @ sk_A) @ 
% 9.61/9.84         (k10_relat_1 @ sk_D @ sk_B)) @ 
% 9.61/9.84        (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('demod', [status(thm)], ['45', '46'])).
% 9.61/9.84  thf('48', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.61/9.84          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['9', '10'])).
% 9.61/9.84  thf('49', plain,
% 9.61/9.84      (((k2_xboole_0 @ (k10_relat_1 @ sk_D @ sk_A) @ 
% 9.61/9.84         (k10_relat_1 @ sk_D @ sk_B)) = (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('sup-', [status(thm)], ['47', '48'])).
% 9.61/9.84  thf('50', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.61/9.84      inference('demod', [status(thm)], ['29', '30'])).
% 9.61/9.84  thf('51', plain,
% 9.61/9.84      (![X0 : $i]:
% 9.61/9.84         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))),
% 9.61/9.84      inference('demod', [status(thm)], ['15', '16', '17'])).
% 9.61/9.84  thf('52', plain,
% 9.61/9.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 9.61/9.84         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 9.61/9.84      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.61/9.84  thf('53', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 9.61/9.84          (k2_xboole_0 @ X1 @ (k10_relat_1 @ sk_D @ X0)))),
% 9.61/9.84      inference('sup-', [status(thm)], ['51', '52'])).
% 9.61/9.84  thf('54', plain,
% 9.61/9.84      (![X0 : $i, X1 : $i]:
% 9.61/9.84         (r1_tarski @ (k10_relat_1 @ sk_C @ X1) @ 
% 9.61/9.84          (k2_xboole_0 @ (k10_relat_1 @ sk_D @ X1) @ X0))),
% 9.61/9.84      inference('sup+', [status(thm)], ['50', '53'])).
% 9.61/9.84  thf('55', plain,
% 9.61/9.84      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 9.61/9.84      inference('sup+', [status(thm)], ['49', '54'])).
% 9.61/9.84  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 9.61/9.84  
% 9.61/9.84  % SZS output end Refutation
% 9.61/9.84  
% 9.61/9.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
