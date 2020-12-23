%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y4o1VaeElh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 ( 787 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t47_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A )
            & ( v1_funct_1 @ C )
            & ( v5_ordinal1 @ C ) )
         => ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ B )
            & ( v1_funct_1 @ C )
            & ( v5_ordinal1 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ C @ A )
              & ( v1_funct_1 @ C )
              & ( v5_ordinal1 @ C ) )
           => ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ C @ B )
              & ( v1_funct_1 @ C )
              & ( v5_ordinal1 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_ordinal1])).

thf('0',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v5_ordinal1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ sk_C @ sk_B )
   <= ~ ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v5_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v5_ordinal1 @ sk_C )
   <= ~ ( v5_ordinal1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v5_ordinal1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_relat_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v5_relat_1 @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v5_ordinal1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','7','10','11'])).

thf('13',plain,(
    ~ ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v5_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( v5_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['13','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y4o1VaeElh
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:53:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 60 iterations in 0.022s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.49  thf(t47_ordinal1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.49             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.22/0.49           ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.22/0.49             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( r1_tarski @ A @ B ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.49                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.22/0.49              ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.22/0.49                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t47_ordinal1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.49        | ~ (v5_relat_1 @ sk_C @ sk_B)
% 0.22/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.49        | ~ (v5_ordinal1 @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (v5_relat_1 @ sk_C @ sk_B)) <= (~ ((v5_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain, ((v5_ordinal1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('3', plain, ((~ (v5_ordinal1 @ sk_C)) <= (~ ((v5_ordinal1 @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('4', plain, (((v5_ordinal1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('7', plain, (((v1_funct_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain, ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_relat_1 @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('10', plain, (((v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (~ ((v5_relat_1 @ sk_C @ sk_B)) | ~ ((v1_relat_1 @ sk_C)) | 
% 0.22/0.49       ~ ((v1_funct_1 @ sk_C)) | ~ ((v5_ordinal1 @ sk_C))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('12', plain, (~ ((v5_relat_1 @ sk_C @ sk_B))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['4', '7', '10', '11'])).
% 0.22/0.49  thf('13', plain, (~ (v5_relat_1 @ sk_C @ sk_B)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.22/0.49  thf('14', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d19_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         (~ (v5_relat_1 @ X27 @ X28)
% 0.22/0.49          | (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.22/0.49          | ~ (v1_relat_1 @ X27))),
% 0.22/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X2 : $i, X4 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf(t48_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.49           = (k3_xboole_0 @ X9 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k2_relat_1 @ sk_C) @ k1_xboole_0)
% 0.22/0.49         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('23', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.49           = (k3_xboole_0 @ X9 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t109_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.22/0.49      inference('sup+', [status(thm)], ['26', '29'])).
% 0.22/0.49  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.22/0.49      inference('sup+', [status(thm)], ['25', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.22/0.49          | (v5_relat_1 @ X27 @ X28)
% 0.22/0.49          | ~ (v1_relat_1 @ X27))),
% 0.22/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.49  thf('33', plain, ((~ (v1_relat_1 @ sk_C) | (v5_relat_1 @ sk_C @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, ($false), inference('demod', [status(thm)], ['13', '35'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
