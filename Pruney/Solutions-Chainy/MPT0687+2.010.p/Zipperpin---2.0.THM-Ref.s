%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iZiXVvjMS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  473 ( 738 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('0',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X22 @ X24 ) @ X23 )
        = ( k2_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
          = ( k2_tarski @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k2_tarski @ sk_A @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('13',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
      & ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('25',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( ( k10_relat_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','25','26','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iZiXVvjMS
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 65 iterations in 0.026s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(t142_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.48         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ B ) =>
% 0.20/0.48          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.48            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.48        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.48        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(t53_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.48       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X22 @ X23)
% 0.20/0.48          | ~ (r2_hidden @ X24 @ X23)
% 0.20/0.48          | ((k3_xboole_0 @ (k2_tarski @ X22 @ X24) @ X23)
% 0.20/0.48              = (k2_tarski @ X22 @ X24)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ (k2_relat_1 @ sk_B_1))
% 0.20/0.48             = (k2_tarski @ sk_A @ X0))
% 0.20/0.48           | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.20/0.48          = (k2_tarski @ sk_A @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('8', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('9', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.20/0.48          = (k1_tarski @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(t173_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X25 : $i, X26 : $i]:
% 0.20/0.48         (((k10_relat_1 @ X25 @ X26) != (k1_xboole_0))
% 0.20/0.48          | (r1_xboole_0 @ (k2_relat_1 @ X25) @ X26)
% 0.20/0.48          | ~ (v1_relat_1 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.48         | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48         | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf(t4_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.48          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((v1_xboole_0 @ 
% 0.20/0.48         (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B_1))))
% 0.20/0.48         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))) & 
% 0.20/0.48             (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '22'])).
% 0.20/0.48  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.48  thf('24', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.48       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(l27_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X20) @ X21) | (r2_hidden @ X20 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X25 : $i, X26 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k2_relat_1 @ X25) @ X26)
% 0.20/0.48          | ((k10_relat_1 @ X25 @ X26) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.48         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.20/0.48             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.48       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.48  thf('39', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '25', '26', '38'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
