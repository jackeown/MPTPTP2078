%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VD2T6l0dg1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:20 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 161 expanded)
%              Number of leaves         :   30 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 (1155 expanded)
%              Number of equality atoms :   59 ( 152 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42
        = ( k2_relat_1 @ X39 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X42 @ X39 ) @ ( sk_C @ X42 @ X39 ) ) @ X39 )
      | ( r2_hidden @ ( sk_C @ X42 @ X39 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X29 @ X30 ) )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['5','15'])).

thf('17',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('20',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_tarski @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('24',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X44 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('30',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('37',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,
    ( ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('45',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VD2T6l0dg1
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 313 iterations in 0.087s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.53  thf(cc1_relat_1, axiom,
% 0.37/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.53  thf('0', plain, (![X36 : $i]: ((v1_relat_1 @ X36) | ~ (v1_xboole_0 @ X36))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.53  thf(d5_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.37/0.53       ( ![C:$i]:
% 0.37/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      (![X39 : $i, X42 : $i]:
% 0.37/0.53         (((X42) = (k2_relat_1 @ X39))
% 0.37/0.53          | (r2_hidden @ 
% 0.37/0.53             (k4_tarski @ (sk_D @ X42 @ X39) @ (sk_C @ X42 @ X39)) @ X39)
% 0.37/0.53          | (r2_hidden @ (sk_C @ X42 @ X39) @ X42))),
% 0.37/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.37/0.53  thf(l1_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X26 : $i, X28 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.37/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.37/0.53          | ((X1) = (k2_relat_1 @ X0))
% 0.37/0.53          | (r1_tarski @ 
% 0.37/0.53             (k1_tarski @ (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0))) @ 
% 0.37/0.53             X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.53  thf(t3_xboole_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.37/0.53          | ((k1_tarski @ 
% 0.37/0.53              (k4_tarski @ (sk_D @ X0 @ k1_xboole_0) @ 
% 0.37/0.53               (sk_C @ X0 @ k1_xboole_0)))
% 0.37/0.53              = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.53  thf(t69_enumset1, axiom,
% 0.37/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.53  thf('6', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.37/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.53  thf(t20_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.53         ( k1_tarski @ A ) ) <=>
% 0.37/0.53       ( ( A ) != ( B ) ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X31 : $i, X32 : $i]:
% 0.37/0.53         (((X32) != (X31))
% 0.37/0.53          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.37/0.53              != (k1_tarski @ X32)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X31 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.37/0.53           != (k1_tarski @ X31))),
% 0.37/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.37/0.53           != (k1_tarski @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.37/0.53  thf(t19_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.37/0.53       ( k1_tarski @ A ) ))).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X29 : $i, X30 : $i]:
% 0.37/0.53         ((k3_xboole_0 @ (k1_tarski @ X29) @ (k2_tarski @ X29 @ X30))
% 0.37/0.53           = (k1_tarski @ X29))),
% 0.37/0.53      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.37/0.53  thf(t100_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.53  thf('11', plain,
% 0.37/0.53      (![X1 : $i, X2 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.53           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.37/0.53           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.53  thf(t92_xboole_1, axiom,
% 0.37/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf('13', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.37/0.53           = (k1_xboole_0))),
% 0.37/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.53  thf('15', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.37/0.53          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.37/0.53      inference('clc', [status(thm)], ['5', '15'])).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      (![X26 : $i, X28 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.37/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.37/0.53          | (r1_tarski @ (k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.53  thf('20', plain,
% 0.37/0.53      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.37/0.53        | ((k1_tarski @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.53  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.37/0.53  thf('22', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.37/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.37/0.53  thf(t7_xboole_0, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.53  thf(t18_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ B ) =>
% 0.37/0.53       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.37/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (![X44 : $i, X45 : $i]:
% 0.37/0.53         ((r2_hidden @ (sk_C_1 @ X44) @ (k2_relat_1 @ X44))
% 0.37/0.53          | ~ (r2_hidden @ X45 @ (k1_relat_1 @ X44))
% 0.37/0.53          | ~ (v1_relat_1 @ X44))),
% 0.37/0.53      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.37/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.53        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.53        | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['0', '26'])).
% 0.37/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.53  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.53        | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.37/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.53  thf(t60_relat_1, conjecture,
% 0.37/0.53    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.37/0.53        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.53      inference('split', [status(esa)], ['30'])).
% 0.37/0.53  thf('32', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.37/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.37/0.53  thf('33', plain,
% 0.37/0.53      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.53      inference('split', [status(esa)], ['30'])).
% 0.37/0.53  thf('34', plain,
% 0.37/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.53         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.53  thf('35', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.53  thf('36', plain,
% 0.37/0.53      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.53       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.53      inference('split', [status(esa)], ['30'])).
% 0.37/0.53  thf('37', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.53      inference('simpl_trail', [status(thm)], ['31', '37'])).
% 0.37/0.53  thf('39', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.37/0.53      inference('simplify_reflect-', [status(thm)], ['29', '38'])).
% 0.37/0.53  thf('40', plain,
% 0.37/0.53      (![X26 : $i, X28 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.37/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      ((r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)),
% 0.37/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.53  thf('43', plain, (((k1_tarski @ (sk_C_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.53  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.37/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.37/0.53  thf('45', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.53  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
