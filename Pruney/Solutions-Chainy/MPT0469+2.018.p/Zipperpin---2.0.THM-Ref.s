%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1plviZws1n

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  435 ( 856 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
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

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('11',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('13',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( ( k3_xboole_0 @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('32',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('42',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','42'])).

thf('44',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['34','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1plviZws1n
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:52:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 39 iterations in 0.026s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(cc1_relat_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.49  thf('0', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf('2', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.49  thf(d4_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X13 : $i, X16 : $i]:
% 0.22/0.49         (((X16) = (k1_relat_1 @ X13))
% 0.22/0.49          | (r2_hidden @ 
% 0.22/0.49             (k4_tarski @ (sk_C_1 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 0.22/0.49          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.49  thf(t2_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.49  thf('7', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.49          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.49  thf('10', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('11', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf(t37_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.22/0.49         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         (((k1_relat_1 @ X20) = (k2_relat_1 @ (k4_relat_1 @ X20)))
% 0.22/0.49          | ~ (v1_relat_1 @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         (((k2_relat_1 @ X20) = (k1_relat_1 @ (k4_relat_1 @ X20)))
% 0.22/0.49          | ~ (v1_relat_1 @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.49  thf(t22_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k3_xboole_0 @
% 0.22/0.49           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.49         ( A ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X19 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X19 @ 
% 0.22/0.49            (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19))) = (
% 0.22/0.49            X19))
% 0.22/0.49          | ~ (v1_relat_1 @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k4_relat_1 @ X0) @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.22/0.49              (k2_relat_1 @ (k4_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X1 @ (k4_relat_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k4_relat_1 @ X0) @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (r2_hidden @ X1 @ (k4_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.22/0.49          | ~ (r2_hidden @ X1 @ (k4_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ (k4_relat_1 @ X0) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k4_relat_1 @ k1_xboole_0) @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k4_relat_1 @ k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '19'])).
% 0.22/0.49  thf(t113_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.49  thf('23', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k4_relat_1 @ k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '22', '23'])).
% 0.22/0.49  thf(dt_k4_relat_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X18 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X18)) | ~ (v1_relat_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ (k4_relat_1 @ k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '26'])).
% 0.22/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.49  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X20 : $i]:
% 0.22/0.49         (((k2_relat_1 @ X20) = (k1_relat_1 @ (k4_relat_1 @ X20)))
% 0.22/0.49          | ~ (v1_relat_1 @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((((k2_relat_1 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf(t60_relat_1, conjecture,
% 0.22/0.49    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.49     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.49        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.49         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['35'])).
% 0.22/0.49  thf('37', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['35'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.49       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('split', [status(esa)], ['35'])).
% 0.22/0.49  thf('42', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.22/0.49  thf('43', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['36', '42'])).
% 0.22/0.49  thf('44', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['34', '43'])).
% 0.22/0.49  thf('45', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '44'])).
% 0.22/0.49  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.49  thf('47', plain, ($false), inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
