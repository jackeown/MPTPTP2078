%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9drlv2Zon3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  563 ( 890 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k9_relat_1 @ X45 @ ( k3_xboole_0 @ X46 @ X47 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X45 @ X46 ) @ ( k9_relat_1 @ X45 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k9_relat_1 @ X45 @ ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X45 @ X46 ) @ ( k9_relat_1 @ X45 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','22'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X44: $i] :
      ( ( ( k9_relat_1 @ X44 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k9_relat_1 @ X45 @ ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X45 @ X46 ) @ ( k9_relat_1 @ X45 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('27',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9drlv2Zon3
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 172 iterations in 0.075s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(t125_funct_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.54         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.54        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.54            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.22/0.54  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t83_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.54  thf(t48_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.54           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.54  thf(t12_setfam_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.54           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (((k4_xboole_0 @ sk_A @ sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['2', '5'])).
% 0.22/0.54  thf(t3_boole, axiom,
% 0.22/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.54  thf('7', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.54           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X0 @ X0)
% 0.22/0.54           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(t2_boole, axiom,
% 0.22/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X8 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '13'])).
% 0.22/0.54  thf(t121_funct_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54       ( ( v2_funct_1 @ C ) =>
% 0.22/0.54         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.22/0.54           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.54         (~ (v2_funct_1 @ X45)
% 0.22/0.54          | ((k9_relat_1 @ X45 @ (k3_xboole_0 @ X46 @ X47))
% 0.22/0.54              = (k3_xboole_0 @ (k9_relat_1 @ X45 @ X46) @ 
% 0.22/0.54                 (k9_relat_1 @ X45 @ X47)))
% 0.22/0.54          | ~ (v1_funct_1 @ X45)
% 0.22/0.54          | ~ (v1_relat_1 @ X45))),
% 0.22/0.54      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.54         (~ (v2_funct_1 @ X45)
% 0.22/0.54          | ((k9_relat_1 @ X45 @ (k1_setfam_1 @ (k2_tarski @ X46 @ X47)))
% 0.22/0.54              = (k1_setfam_1 @ 
% 0.22/0.54                 (k2_tarski @ (k9_relat_1 @ X45 @ X46) @ 
% 0.22/0.54                  (k9_relat_1 @ X45 @ X47))))
% 0.22/0.54          | ~ (v1_funct_1 @ X45)
% 0.22/0.54          | ~ (v1_relat_1 @ X45))),
% 0.22/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.54  thf(t4_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X4 @ X5)
% 0.22/0.54          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X4 @ X5)
% 0.22/0.54          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ 
% 0.22/0.54             (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((r2_hidden @ 
% 0.22/0.54           (sk_C_1 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.22/0.54           (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.22/0.54          | ~ (v1_relat_1 @ X2)
% 0.22/0.54          | ~ (v1_funct_1 @ X2)
% 0.22/0.54          | ~ (v2_funct_1 @ X2)
% 0.22/0.54          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ 
% 0.22/0.54           (sk_C_1 @ (k9_relat_1 @ X0 @ sk_B) @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.22/0.54           (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '22'])).
% 0.22/0.54  thf(t149_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X44 : $i]:
% 0.22/0.54         (((k9_relat_1 @ X44 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X44))),
% 0.22/0.54      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X8 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.54         (~ (v2_funct_1 @ X45)
% 0.22/0.54          | ((k9_relat_1 @ X45 @ (k1_setfam_1 @ (k2_tarski @ X46 @ X47)))
% 0.22/0.54              = (k1_setfam_1 @ 
% 0.22/0.54                 (k2_tarski @ (k9_relat_1 @ X45 @ X46) @ 
% 0.22/0.54                  (k9_relat_1 @ X45 @ X47))))
% 0.22/0.54          | ~ (v1_funct_1 @ X45)
% 0.22/0.54          | ~ (v1_relat_1 @ X45))),
% 0.22/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.22/0.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X42 : $i, X43 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.22/0.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X3 @ 
% 0.22/0.54             (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.22/0.54          | ~ (v1_relat_1 @ X2)
% 0.22/0.54          | ~ (v1_funct_1 @ X2)
% 0.22/0.54          | ~ (v2_funct_1 @ X2)
% 0.22/0.54          | ~ (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.54          | ~ (r1_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.22/0.54               (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.54          | ~ (v2_funct_1 @ X1)
% 0.22/0.54          | ~ (v1_funct_1 @ X1)
% 0.22/0.54          | ~ (v1_relat_1 @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['25', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (~ (r1_xboole_0 @ (k9_relat_1 @ X0 @ X1) @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '31'])).
% 0.22/0.54  thf('33', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X12 : $i, X14 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['32', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v2_funct_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.22/0.54          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C_2)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_C_2)
% 0.22/0.54        | ~ (v2_funct_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('44', plain, ((v1_funct_1 @ sk_C_2)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('45', plain, ((v2_funct_1 @ sk_C_2)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('46', plain, ($false),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
