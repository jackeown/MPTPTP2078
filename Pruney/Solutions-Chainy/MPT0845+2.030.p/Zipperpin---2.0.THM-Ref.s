%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8zhPADqrwP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  310 ( 412 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('7',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5','8','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('15',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_A )
      | ~ ( r1_xboole_0 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_A )
      | ~ ( r1_xboole_0 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X19: $i] :
      ~ ( r2_hidden @ X19 @ sk_A ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8zhPADqrwP
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 105 iterations in 0.060s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(t60_relat_1, axiom,
% 0.22/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.52  thf(d5_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.52               ( ?[D:$i]:
% 0.22/0.52                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.22/0.52                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_C_2 @ X8 @ X9) @ X8)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 0.22/0.52          | ((X8) = (k2_relat_1 @ X9))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (v1_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.22/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.53          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.53          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.53  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.53  thf(fc3_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.53  thf('4', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.53  thf('5', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.53  thf('7', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.53  thf('8', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['2', '5', '8', '9'])).
% 0.22/0.53  thf(t7_ordinal1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ~ (r1_tarski @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.53  thf('13', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf(t1_mcart_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53             ( ![B:$i]:
% 0.22/0.53               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X19 : $i]: (~ (r2_hidden @ X19 @ sk_A) | ~ (r1_xboole_0 @ X19 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf(t7_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ~( ( r2_hidden @ A @ B ) & 
% 0.22/0.53          ( ![C:$i]:
% 0.22/0.53            ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.53                 ( ![D:$i]:
% 0.22/0.53                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X5 @ X6) | (r2_hidden @ (sk_C_1 @ X6) @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_tarski])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X19 : $i]: (~ (r2_hidden @ X19 @ sk_A) | ~ (r1_xboole_0 @ X19 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.22/0.53          | ~ (r2_hidden @ X7 @ X6)
% 0.22/0.53          | ~ (r2_hidden @ X7 @ (sk_C_1 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_tarski])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.53      inference('condensation', [status(thm)], ['23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.22/0.53          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.22/0.53          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '25'])).
% 0.22/0.53  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.22/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.53  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['20', '27'])).
% 0.22/0.53  thf('29', plain, (![X19 : $i]: ~ (r2_hidden @ X19 @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '28'])).
% 0.22/0.53  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['14', '29'])).
% 0.22/0.53  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('32', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
