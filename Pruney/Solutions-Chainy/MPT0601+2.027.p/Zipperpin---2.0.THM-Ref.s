%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wfRemf8HT

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  454 (1158 expanded)
%              Number of equality atoms :   43 ( 111 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ X39 @ ( k1_tarski @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( ( k9_relat_1 @ X41 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('11',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ X39 @ ( k1_tarski @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X33 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 )
      | ~ ( r1_tarski @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( ( k9_relat_1 @ X44 @ X43 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('20',plain,
    ( ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['9','31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['7','33'])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','31'])).

thf('43',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wfRemf8HT
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 63 iterations in 0.024s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(d16_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X39 : $i, X40 : $i]:
% 0.20/0.45         (((k11_relat_1 @ X39 @ X40) = (k9_relat_1 @ X39 @ (k1_tarski @ X40)))
% 0.20/0.45          | ~ (v1_relat_1 @ X39))),
% 0.20/0.45      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.45  thf(l27_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X31 : $i, X32 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 0.20/0.45      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf(t151_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X41 : $i, X42 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ (k1_relat_1 @ X41) @ X42)
% 0.20/0.45          | ((k9_relat_1 @ X41 @ X42) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X41))),
% 0.20/0.45      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k9_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(t205_relat_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.45         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ B ) =>
% 0.20/0.45          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.45            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.45        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.45         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.20/0.45        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.45       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.45         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X39 : $i, X40 : $i]:
% 0.20/0.45         (((k11_relat_1 @ X39 @ X40) = (k9_relat_1 @ X39 @ (k1_tarski @ X40)))
% 0.20/0.45          | ~ (v1_relat_1 @ X39))),
% 0.20/0.45      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf(t38_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.45       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.20/0.45         ((r1_tarski @ (k2_tarski @ X33 @ X35) @ X36)
% 0.20/0.45          | ~ (r2_hidden @ X35 @ X36)
% 0.20/0.45          | ~ (r2_hidden @ X33 @ X36))),
% 0.20/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      ((![X0 : $i]:
% 0.20/0.45          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.45           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.45  thf(t69_enumset1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.45  thf('17', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf(t152_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.45            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.45            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      (![X43 : $i, X44 : $i]:
% 0.20/0.45         (((X43) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X44)
% 0.20/0.45          | ~ (r1_tarski @ X43 @ (k1_relat_1 @ X44))
% 0.20/0.45          | ((k9_relat_1 @ X44 @ X43) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.45         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.45         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      (((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.45         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf(t1_boole, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.45  thf('23', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.45  thf(t49_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (![X37 : $i, X38 : $i]:
% 0.20/0.45         ((k2_xboole_0 @ (k1_tarski @ X37) @ X38) != (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.45  thf('25', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      (((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '26'])).
% 0.20/0.45  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.20/0.45      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.20/0.45             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '29'])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.20/0.45       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.45  thf('32', plain,
% 0.20/0.45      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.20/0.45       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('split', [status(esa)], ['6'])).
% 0.20/0.45  thf('33', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['9', '31', '32'])).
% 0.20/0.45  thf('34', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['7', '33'])).
% 0.20/0.45  thf('35', plain,
% 0.20/0.45      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '34'])).
% 0.20/0.45  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.45  thf('38', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.45      inference('sup+', [status(thm)], ['0', '37'])).
% 0.20/0.45  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('40', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.45         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('42', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['9', '31'])).
% 0.20/0.45  thf('43', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.20/0.45  thf('44', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
