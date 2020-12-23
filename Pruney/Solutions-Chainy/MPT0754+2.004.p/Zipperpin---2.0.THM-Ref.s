%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Av0QkJP1lk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 688 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['13','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Av0QkJP1lk
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:08:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 20 iterations in 0.011s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.48  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t47_ordinal1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.48             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.22/0.48           ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.22/0.48             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48          ( ![C:$i]:
% 0.22/0.48            ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.48                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.22/0.48              ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.22/0.48                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t47_ordinal1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.48        | ~ (v5_relat_1 @ sk_C @ sk_B)
% 0.22/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.48        | ~ (v5_ordinal1 @ sk_C))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((~ (v5_relat_1 @ sk_C @ sk_B)) <= (~ ((v5_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain, ((v5_ordinal1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('3', plain, ((~ (v5_ordinal1 @ sk_C)) <= (~ ((v5_ordinal1 @ sk_C)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('4', plain, (((v5_ordinal1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('7', plain, (((v1_funct_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_relat_1 @ sk_C)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('10', plain, (((v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (~ ((v5_relat_1 @ sk_C @ sk_B)) | ~ ((v1_relat_1 @ sk_C)) | 
% 0.22/0.48       ~ ((v1_funct_1 @ sk_C)) | ~ ((v5_ordinal1 @ sk_C))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('12', plain, (~ ((v5_relat_1 @ sk_C @ sk_B))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '7', '10', '11'])).
% 0.22/0.48  thf('13', plain, (~ (v5_relat_1 @ sk_C @ sk_B)),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.22/0.48  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d19_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (v5_relat_1 @ X3 @ X4)
% 0.22/0.48          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.22/0.48          | ~ (v1_relat_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf(t1_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.48       ( r1_tarski @ A @ C ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.48          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.48          | (r1_tarski @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.22/0.48          | (v5_relat_1 @ X3 @ X4)
% 0.22/0.48          | ~ (v1_relat_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.48  thf('24', plain, ((~ (v1_relat_1 @ sk_C) | (v5_relat_1 @ sk_C @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf('27', plain, ($false), inference('demod', [status(thm)], ['13', '26'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
