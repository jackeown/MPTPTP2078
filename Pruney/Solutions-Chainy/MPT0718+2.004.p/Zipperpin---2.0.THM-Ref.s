%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZG98d6VbSa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:24 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 115 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  520 (1053 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t173_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v5_funct_1 @ A @ B )
              & ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) ) )
           => ( v2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v5_funct_1 @ A @ B )
                & ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) ) )
             => ( v2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_funct_1])).

thf('0',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_relat_1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_1 @ X12 @ ( sk_B @ X12 ) ) )
      | ( v2_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v5_funct_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_B @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v5_funct_1 @ X14 @ X15 )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X16 ) @ ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ X20 @ ( k2_tarski @ X19 @ X21 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X20 @ X19 ) @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k2_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','34','42','43','44'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['49'])).

thf('51',plain,(
    v2_relat_1 @ sk_B_1 ),
    inference(clc,[status(thm)],['25','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZG98d6VbSa
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.37/3.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.37/3.59  % Solved by: fo/fo7.sh
% 3.37/3.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.37/3.59  % done 4245 iterations in 3.168s
% 3.37/3.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.37/3.59  % SZS output start Refutation
% 3.37/3.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.37/3.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.37/3.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.37/3.59  thf(sk_B_type, type, sk_B: $i > $i).
% 3.37/3.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.37/3.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.37/3.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.37/3.59  thf(sk_A_type, type, sk_A: $i).
% 3.37/3.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.37/3.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.37/3.59  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 3.37/3.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.37/3.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.37/3.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.37/3.59  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 3.37/3.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.37/3.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.37/3.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.37/3.59  thf(t173_funct_1, conjecture,
% 3.37/3.59    (![A:$i]:
% 3.37/3.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.59       ( ![B:$i]:
% 3.37/3.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.37/3.59           ( ( ( v5_funct_1 @ A @ B ) & 
% 3.37/3.59               ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 3.37/3.59             ( v2_relat_1 @ B ) ) ) ) ))).
% 3.37/3.59  thf(zf_stmt_0, negated_conjecture,
% 3.37/3.59    (~( ![A:$i]:
% 3.37/3.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.59          ( ![B:$i]:
% 3.37/3.59            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.37/3.59              ( ( ( v5_funct_1 @ A @ B ) & 
% 3.37/3.59                  ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 3.37/3.59                ( v2_relat_1 @ B ) ) ) ) ) )),
% 3.37/3.59    inference('cnf.neg', [status(esa)], [t173_funct_1])).
% 3.37/3.59  thf('0', plain, (~ (v2_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf(d15_funct_1, axiom,
% 3.37/3.59    (![A:$i]:
% 3.37/3.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.59       ( ( v2_relat_1 @ A ) <=>
% 3.37/3.59         ( ![B:$i]:
% 3.37/3.59           ( ~( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 3.37/3.59                ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) ) ))).
% 3.37/3.59  thf('1', plain,
% 3.37/3.59      (![X12 : $i]:
% 3.37/3.59         ((v1_xboole_0 @ (k1_funct_1 @ X12 @ (sk_B @ X12)))
% 3.37/3.59          | (v2_relat_1 @ X12)
% 3.37/3.59          | ~ (v1_funct_1 @ X12)
% 3.37/3.59          | ~ (v1_relat_1 @ X12))),
% 3.37/3.59      inference('cnf', [status(esa)], [d15_funct_1])).
% 3.37/3.59  thf(l13_xboole_0, axiom,
% 3.37/3.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.37/3.59  thf('2', plain,
% 3.37/3.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.37/3.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.37/3.59  thf('3', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_funct_1 @ X0)
% 3.37/3.59          | (v2_relat_1 @ X0)
% 3.37/3.59          | ((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['1', '2'])).
% 3.37/3.59  thf('4', plain, ((v5_funct_1 @ sk_A @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('5', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('6', plain,
% 3.37/3.59      (![X12 : $i]:
% 3.37/3.59         ((r2_hidden @ (sk_B @ X12) @ (k1_relat_1 @ X12))
% 3.37/3.59          | (v2_relat_1 @ X12)
% 3.37/3.59          | ~ (v1_funct_1 @ X12)
% 3.37/3.59          | ~ (v1_relat_1 @ X12))),
% 3.37/3.59      inference('cnf', [status(esa)], [d15_funct_1])).
% 3.37/3.59  thf('7', plain,
% 3.37/3.59      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 3.37/3.59        | ~ (v1_relat_1 @ sk_B_1)
% 3.37/3.59        | ~ (v1_funct_1 @ sk_B_1)
% 3.37/3.59        | (v2_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('sup+', [status(thm)], ['5', '6'])).
% 3.37/3.59  thf('8', plain, ((v1_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('9', plain, ((v1_funct_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('10', plain,
% 3.37/3.59      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 3.37/3.59        | (v2_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.37/3.59  thf('11', plain, (~ (v2_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('12', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 3.37/3.59      inference('clc', [status(thm)], ['10', '11'])).
% 3.37/3.59  thf(d20_funct_1, axiom,
% 3.37/3.59    (![A:$i]:
% 3.37/3.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.59       ( ![B:$i]:
% 3.37/3.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.37/3.59           ( ( v5_funct_1 @ B @ A ) <=>
% 3.37/3.59             ( ![C:$i]:
% 3.37/3.59               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 3.37/3.59                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.37/3.59  thf('13', plain,
% 3.37/3.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.37/3.59         (~ (v1_relat_1 @ X14)
% 3.37/3.59          | ~ (v1_funct_1 @ X14)
% 3.37/3.59          | ~ (v5_funct_1 @ X14 @ X15)
% 3.37/3.59          | (r2_hidden @ (k1_funct_1 @ X14 @ X16) @ (k1_funct_1 @ X15 @ X16))
% 3.37/3.59          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 3.37/3.59          | ~ (v1_funct_1 @ X15)
% 3.37/3.59          | ~ (v1_relat_1 @ X15))),
% 3.37/3.59      inference('cnf', [status(esa)], [d20_funct_1])).
% 3.37/3.59  thf('14', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_funct_1 @ X0)
% 3.37/3.59          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 3.37/3.59             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 3.37/3.59          | ~ (v5_funct_1 @ sk_A @ X0)
% 3.37/3.59          | ~ (v1_funct_1 @ sk_A)
% 3.37/3.59          | ~ (v1_relat_1 @ sk_A))),
% 3.37/3.59      inference('sup-', [status(thm)], ['12', '13'])).
% 3.37/3.59  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('17', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_funct_1 @ X0)
% 3.37/3.59          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 3.37/3.59             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 3.37/3.59          | ~ (v5_funct_1 @ sk_A @ X0))),
% 3.37/3.59      inference('demod', [status(thm)], ['14', '15', '16'])).
% 3.37/3.59  thf('18', plain,
% 3.37/3.59      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 3.37/3.59         (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 3.37/3.59        | ~ (v1_funct_1 @ sk_B_1)
% 3.37/3.59        | ~ (v1_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('sup-', [status(thm)], ['4', '17'])).
% 3.37/3.59  thf('19', plain, ((v1_funct_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('21', plain,
% 3.37/3.59      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 3.37/3.59        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 3.37/3.59      inference('demod', [status(thm)], ['18', '19', '20'])).
% 3.37/3.59  thf('22', plain,
% 3.37/3.59      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 3.37/3.59        | (v2_relat_1 @ sk_B_1)
% 3.37/3.59        | ~ (v1_funct_1 @ sk_B_1)
% 3.37/3.59        | ~ (v1_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('sup+', [status(thm)], ['3', '21'])).
% 3.37/3.59  thf('23', plain, ((v1_funct_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('25', plain,
% 3.37/3.59      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 3.37/3.59        | (v2_relat_1 @ sk_B_1))),
% 3.37/3.59      inference('demod', [status(thm)], ['22', '23', '24'])).
% 3.37/3.59  thf(t60_relat_1, axiom,
% 3.37/3.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.37/3.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.37/3.59  thf('26', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.37/3.59  thf(t118_funct_1, axiom,
% 3.37/3.59    (![A:$i,B:$i,C:$i]:
% 3.37/3.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.37/3.59       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 3.37/3.59           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 3.37/3.59         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 3.37/3.59           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 3.37/3.59  thf('27', plain,
% 3.37/3.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.37/3.59         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 3.37/3.59          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 3.37/3.59          | ((k9_relat_1 @ X20 @ (k2_tarski @ X19 @ X21))
% 3.37/3.59              = (k2_tarski @ (k1_funct_1 @ X20 @ X19) @ 
% 3.37/3.59                 (k1_funct_1 @ X20 @ X21)))
% 3.37/3.59          | ~ (v1_funct_1 @ X20)
% 3.37/3.59          | ~ (v1_relat_1 @ X20))),
% 3.37/3.59      inference('cnf', [status(esa)], [t118_funct_1])).
% 3.37/3.59  thf('28', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 3.37/3.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.37/3.59          | ~ (v1_funct_1 @ k1_xboole_0)
% 3.37/3.59          | ((k9_relat_1 @ k1_xboole_0 @ (k2_tarski @ X0 @ X1))
% 3.37/3.59              = (k2_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 3.37/3.59                 (k1_funct_1 @ k1_xboole_0 @ X1)))
% 3.37/3.59          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['26', '27'])).
% 3.37/3.59  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf(t110_relat_1, axiom,
% 3.37/3.59    (![A:$i]:
% 3.37/3.59     ( ( v1_relat_1 @ A ) =>
% 3.37/3.59       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 3.37/3.59  thf('30', plain,
% 3.37/3.59      (![X10 : $i]:
% 3.37/3.59         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 3.37/3.59          | ~ (v1_relat_1 @ X10))),
% 3.37/3.59      inference('cnf', [status(esa)], [t110_relat_1])).
% 3.37/3.59  thf(dt_k7_relat_1, axiom,
% 3.37/3.59    (![A:$i,B:$i]:
% 3.37/3.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.37/3.59  thf('31', plain,
% 3.37/3.59      (![X8 : $i, X9 : $i]:
% 3.37/3.59         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k7_relat_1 @ X8 @ X9)))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.37/3.59  thf('32', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v1_relat_1 @ k1_xboole_0)
% 3.37/3.59          | ~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_relat_1 @ X0))),
% 3.37/3.59      inference('sup+', [status(thm)], ['30', '31'])).
% 3.37/3.59  thf('33', plain,
% 3.37/3.59      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 3.37/3.59      inference('simplify', [status(thm)], ['32'])).
% 3.37/3.59  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.37/3.59      inference('sup-', [status(thm)], ['29', '33'])).
% 3.37/3.59  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('36', plain,
% 3.37/3.59      (![X10 : $i]:
% 3.37/3.59         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 3.37/3.59          | ~ (v1_relat_1 @ X10))),
% 3.37/3.59      inference('cnf', [status(esa)], [t110_relat_1])).
% 3.37/3.59  thf(fc8_funct_1, axiom,
% 3.37/3.59    (![A:$i,B:$i]:
% 3.37/3.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.59       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 3.37/3.59         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 3.37/3.59  thf('37', plain,
% 3.37/3.59      (![X17 : $i, X18 : $i]:
% 3.37/3.59         (~ (v1_funct_1 @ X17)
% 3.37/3.59          | ~ (v1_relat_1 @ X17)
% 3.37/3.59          | (v1_funct_1 @ (k7_relat_1 @ X17 @ X18)))),
% 3.37/3.59      inference('cnf', [status(esa)], [fc8_funct_1])).
% 3.37/3.59  thf('38', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v1_funct_1 @ k1_xboole_0)
% 3.37/3.59          | ~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_relat_1 @ X0)
% 3.37/3.59          | ~ (v1_funct_1 @ X0))),
% 3.37/3.59      inference('sup+', [status(thm)], ['36', '37'])).
% 3.37/3.59  thf('39', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (v1_funct_1 @ X0)
% 3.37/3.59          | ~ (v1_relat_1 @ X0)
% 3.37/3.59          | (v1_funct_1 @ k1_xboole_0))),
% 3.37/3.59      inference('simplify', [status(thm)], ['38'])).
% 3.37/3.59  thf('40', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_A))),
% 3.37/3.59      inference('sup-', [status(thm)], ['35', '39'])).
% 3.37/3.59  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('42', plain, ((v1_funct_1 @ k1_xboole_0)),
% 3.37/3.59      inference('demod', [status(thm)], ['40', '41'])).
% 3.37/3.59  thf(t150_relat_1, axiom,
% 3.37/3.59    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 3.37/3.59  thf('43', plain,
% 3.37/3.59      (![X11 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t150_relat_1])).
% 3.37/3.59  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.37/3.59  thf('45', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 3.37/3.59          | ((k1_xboole_0)
% 3.37/3.59              = (k2_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 3.37/3.59                 (k1_funct_1 @ k1_xboole_0 @ X1)))
% 3.37/3.59          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.37/3.59      inference('demod', [status(thm)], ['28', '34', '42', '43', '44'])).
% 3.37/3.59  thf(t41_enumset1, axiom,
% 3.37/3.59    (![A:$i,B:$i]:
% 3.37/3.59     ( ( k2_tarski @ A @ B ) =
% 3.37/3.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 3.37/3.59  thf('46', plain,
% 3.37/3.59      (![X3 : $i, X4 : $i]:
% 3.37/3.59         ((k2_tarski @ X3 @ X4)
% 3.37/3.59           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 3.37/3.59      inference('cnf', [status(esa)], [t41_enumset1])).
% 3.37/3.59  thf(t49_zfmisc_1, axiom,
% 3.37/3.59    (![A:$i,B:$i]:
% 3.37/3.59     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 3.37/3.59  thf('47', plain,
% 3.37/3.59      (![X6 : $i, X7 : $i]:
% 3.37/3.59         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 3.37/3.59  thf('48', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 3.37/3.59      inference('sup-', [status(thm)], ['46', '47'])).
% 3.37/3.59  thf('49', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.37/3.59      inference('simplify_reflect-', [status(thm)], ['45', '48'])).
% 3.37/3.59  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.37/3.59      inference('condensation', [status(thm)], ['49'])).
% 3.37/3.59  thf('51', plain, ((v2_relat_1 @ sk_B_1)),
% 3.37/3.59      inference('clc', [status(thm)], ['25', '50'])).
% 3.37/3.59  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 3.37/3.59  
% 3.37/3.59  % SZS output end Refutation
% 3.37/3.59  
% 3.37/3.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
