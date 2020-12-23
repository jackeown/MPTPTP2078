%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ouei84319l

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 172 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  458 (1145 expanded)
%              Number of equality atoms :   60 ( 161 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k2_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X48 @ X45 ) @ ( sk_C @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
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

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37 != X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X36 ) )
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('7',plain,(
    ! [X36: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) )
     != ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X36: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X36 ) ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_tarski @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X36: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X36 ) ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
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

thf('25',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( r2_hidden @ X51 @ ( k1_relat_1 @ X50 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

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
    inference(clc,[status(thm)],['21','22'])).

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

thf('39',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,
    ( ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X36 ) ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf('46',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ouei84319l
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 175 iterations in 0.081s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.52  thf(cc1_relat_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.52  thf('0', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.52  thf(d5_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X45 : $i, X48 : $i]:
% 0.20/0.52         (((X48) = (k2_relat_1 @ X45))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_D @ X48 @ X45) @ (sk_C @ X48 @ X45)) @ X45)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X48 @ X45) @ X48))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.52  thf(l1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X33 : $i, X35 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.20/0.52          | ((X1) = (k2_relat_1 @ X0))
% 0.20/0.52          | (r1_tarski @ 
% 0.20/0.52             (k1_tarski @ (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0))) @ 
% 0.20/0.52             X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t3_xboole_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.52          | ((k1_tarski @ 
% 0.20/0.52              (k4_tarski @ (sk_D @ X0 @ k1_xboole_0) @ 
% 0.20/0.52               (sk_C @ X0 @ k1_xboole_0)))
% 0.20/0.52              = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t20_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.52         ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ( A ) != ( B ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X36 : $i, X37 : $i]:
% 0.20/0.52         (((X37) != (X36))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X36))
% 0.20/0.52              != (k1_tarski @ X37)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X36 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))
% 0.20/0.52           != (k1_tarski @ X36))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('8', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t11_setfam_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.52  thf('9', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.20/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X40 : $i, X41 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.52           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(t92_xboole_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('15', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('16', plain, (![X36 : $i]: ((k1_xboole_0) != (k1_tarski @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.52          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['5', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X33 : $i, X35 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.20/0.52        | ((k1_tarski @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, (![X36 : $i]: ((k1_xboole_0) != (k1_tarski @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.20/0.52  thf('23', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf(t7_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf(t18_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X50 : $i, X51 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C_1 @ X50) @ (k2_relat_1 @ X50))
% 0.20/0.52          | ~ (r2_hidden @ X51 @ (k1_relat_1 @ X50))
% 0.20/0.52          | ~ (v1_relat_1 @ X50))),
% 0.20/0.52      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X33 : $i, X35 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)
% 0.20/0.52        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.52        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '28'])).
% 0.20/0.52  thf(t60_relat_1, conjecture,
% 0.20/0.52    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.52     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.52        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['30'])).
% 0.20/0.52  thf('32', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['30'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.52       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['30'])).
% 0.20/0.52  thf('37', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['31', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)
% 0.20/0.52        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['29', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.52        | (r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '39'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.52  thf('44', plain, (((k1_tarski @ (sk_C_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (![X36 : $i]: ((k1_xboole_0) != (k1_tarski @ X36))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.20/0.52  thf('46', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
