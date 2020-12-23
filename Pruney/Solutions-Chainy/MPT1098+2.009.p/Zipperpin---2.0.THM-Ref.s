%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o2JEtuwxE0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:44 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   63 (  96 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  483 ( 934 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_finset_1 @ X15 )
      | ( r1_tarski @ ( sk_E @ X16 @ X17 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('2',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t143_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X12 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X10 @ X13 ) @ ( k2_xboole_0 @ X11 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t143_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X4 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X3 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X3 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X3 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['6','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_finset_1 @ X15 )
      | ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( sk_D @ X16 @ X17 @ X15 ) @ ( sk_E @ X16 @ X17 @ X15 ) ) )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) )
    = ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ~ ( v1_finset_1 @ X18 )
      | ~ ( r1_tarski @ X18 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X18 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_finset_1 @ X15 )
      | ( r1_tarski @ ( sk_D @ X16 @ X17 @ X15 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('36',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_finset_1 @ X15 )
      | ( v1_finset_1 @ ( sk_D @ X16 @ X17 @ X15 ) )
      | ~ ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('41',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['33','38','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o2JEtuwxE0
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 646 iterations in 0.348s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.79  thf(t33_finset_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.59/0.79          ( ![D:$i]:
% 0.59/0.79            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.59/0.79                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.79        ( ~( ( v1_finset_1 @ A ) & 
% 0.59/0.79             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.59/0.79             ( ![D:$i]:
% 0.59/0.79               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.59/0.79                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.59/0.79  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t32_finset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.59/0.79          ( ![D:$i,E:$i]:
% 0.59/0.79            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.59/0.79                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.59/0.79                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (~ (v1_finset_1 @ X15)
% 0.59/0.79          | (r1_tarski @ (sk_E @ X16 @ X17 @ X15) @ X16)
% 0.59/0.79          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (((r1_tarski @ (sk_E @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)
% 0.59/0.79        | ~ (v1_finset_1 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf('3', plain, ((v1_finset_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('4', plain, ((r1_tarski @ (sk_E @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)),
% 0.59/0.79      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf(t12_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (((k2_xboole_0 @ (sk_E @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1) = (sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.79  thf(d3_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X1 : $i, X3 : $i]:
% 0.59/0.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X1 : $i, X3 : $i]:
% 0.59/0.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.79  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.79  thf(t143_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.79     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 0.59/0.79         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 0.59/0.79       ( r1_tarski @
% 0.59/0.79         ( k2_xboole_0 @ A @ B ) @ 
% 0.59/0.79         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X9 @ (k2_zfmisc_1 @ X10 @ X11))
% 0.59/0.79          | ~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X13 @ X14))
% 0.59/0.79          | (r1_tarski @ (k2_xboole_0 @ X9 @ X12) @ 
% 0.59/0.79             (k2_zfmisc_1 @ (k2_xboole_0 @ X10 @ X13) @ 
% 0.59/0.79              (k2_xboole_0 @ X11 @ X14))))),
% 0.59/0.79      inference('cnf', [status(esa)], [t143_zfmisc_1])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         ((r1_tarski @ (k2_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X4) @ 
% 0.59/0.79           (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X3) @ (k2_xboole_0 @ X0 @ X2)))
% 0.59/0.79          | ~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ X3 @ X2)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         (r1_tarski @ 
% 0.59/0.79          (k2_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.59/0.79          (k2_zfmisc_1 @ (k2_xboole_0 @ X3 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['13', '16'])).
% 0.59/0.79  thf(t11_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 0.59/0.79          (k2_zfmisc_1 @ (k2_xboole_0 @ X3 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 0.59/0.79          (k2_zfmisc_1 @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.59/0.79          (k2_zfmisc_1 @ X0 @ sk_C_1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['6', '20'])).
% 0.59/0.79  thf('22', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (~ (v1_finset_1 @ X15)
% 0.59/0.79          | (r1_tarski @ X15 @ 
% 0.59/0.79             (k2_zfmisc_1 @ (sk_D @ X16 @ X17 @ X15) @ (sk_E @ X16 @ X17 @ X15)))
% 0.59/0.79          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (((r1_tarski @ sk_A @ 
% 0.59/0.79         (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.79          (sk_E @ sk_C_1 @ sk_B @ sk_A)))
% 0.59/0.79        | ~ (v1_finset_1 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.79  thf('25', plain, ((v1_finset_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      ((r1_tarski @ sk_A @ 
% 0.59/0.79        (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.79         (sk_E @ sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (((k2_xboole_0 @ sk_A @ 
% 0.59/0.79         (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.79          (sk_E @ sk_C_1 @ sk_B @ sk_A)))
% 0.59/0.79         = (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.79            (sk_E @ sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ 
% 0.59/0.79             (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.59/0.79              (sk_E @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.59/0.79             X0)
% 0.59/0.79          | (r1_tarski @ sk_A @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      ((r1_tarski @ sk_A @ 
% 0.59/0.79        (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['21', '30'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X18 : $i]:
% 0.59/0.79         (~ (v1_finset_1 @ X18)
% 0.59/0.79          | ~ (r1_tarski @ X18 @ sk_B)
% 0.59/0.79          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X18 @ sk_C_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      ((~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.59/0.79        | ~ (v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('34', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (~ (v1_finset_1 @ X15)
% 0.59/0.79          | (r1_tarski @ (sk_D @ X16 @ X17 @ X15) @ X17)
% 0.59/0.79          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.59/0.79        | ~ (v1_finset_1 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.79  thf('37', plain, ((v1_finset_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('38', plain, ((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.59/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.79  thf('39', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (~ (v1_finset_1 @ X15)
% 0.59/0.79          | (v1_finset_1 @ (sk_D @ X16 @ X17 @ X15))
% 0.59/0.79          | ~ (r1_tarski @ X15 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      (((v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.79  thf('42', plain, ((v1_finset_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('43', plain, ((v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain, ($false),
% 0.59/0.79      inference('demod', [status(thm)], ['33', '38', '43'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
