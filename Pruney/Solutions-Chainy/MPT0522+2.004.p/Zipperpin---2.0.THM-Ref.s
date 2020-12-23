%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuqVU138uC

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  257 ( 309 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ A @ A ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( r3_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r3_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X6 @ X7 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k5_relat_1 @ X10 @ X11 ) @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t122_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( r1_tarski @ ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) @ ( k5_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( r1_tarski @ ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) @ ( k5_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t122_relat_1])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) ) @ ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuqVU138uC
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:40:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 24 iterations in 0.020s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(reflexivity_r3_xboole_0, axiom, (![A:$i,B:$i]: ( r3_xboole_0 @ A @ A ))).
% 0.19/0.45  thf('0', plain, (![X3 : $i]: (r3_xboole_0 @ X3 @ X3)),
% 0.19/0.45      inference('cnf', [status(esa)], [reflexivity_r3_xboole_0])).
% 0.19/0.45  thf(d9_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.19/0.45       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((r1_tarski @ X0 @ X1)
% 0.19/0.45          | (r1_tarski @ X1 @ X0)
% 0.19/0.45          | ~ (r3_xboole_0 @ X1 @ X0))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.45  thf(dt_k8_relat_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X4 : $i, X5 : $i]:
% 0.19/0.45         ((v1_relat_1 @ (k8_relat_1 @ X4 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.45  thf(t117_relat_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X6 : $i, X7 : $i]:
% 0.19/0.45         ((r1_tarski @ (k8_relat_1 @ X6 @ X7) @ X7) | ~ (v1_relat_1 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.19/0.45  thf(t50_relat_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( v1_relat_1 @ B ) =>
% 0.19/0.45           ( ![C:$i]:
% 0.19/0.45             ( ( v1_relat_1 @ C ) =>
% 0.19/0.45               ( ![D:$i]:
% 0.19/0.45                 ( ( v1_relat_1 @ D ) =>
% 0.19/0.45                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.19/0.45                     ( r1_tarski @
% 0.19/0.45                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X8)
% 0.19/0.45          | ~ (v1_relat_1 @ X9)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X10 @ X11) @ (k5_relat_1 @ X8 @ X9))
% 0.19/0.45          | ~ (r1_tarski @ X11 @ X9)
% 0.19/0.45          | ~ (r1_tarski @ X10 @ X8)
% 0.19/0.45          | ~ (v1_relat_1 @ X11)
% 0.19/0.45          | ~ (v1_relat_1 @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [t50_relat_1])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X2)
% 0.19/0.45          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45          | ~ (r1_tarski @ X2 @ X3)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.45             (k5_relat_1 @ X3 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X3))),
% 0.19/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X3)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.45             (k5_relat_1 @ X3 @ X0))
% 0.19/0.45          | ~ (r1_tarski @ X2 @ X3)
% 0.19/0.45          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X2)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X2)
% 0.19/0.45          | ~ (r1_tarski @ X2 @ X3)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.45             (k5_relat_1 @ X3 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X3))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '8'])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X3)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.45             (k5_relat_1 @ X3 @ X0))
% 0.19/0.45          | ~ (r1_tarski @ X2 @ X3)
% 0.19/0.45          | ~ (v1_relat_1 @ X2)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X1)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | (r1_tarski @ (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ X1)) @ 
% 0.19/0.45             (k5_relat_1 @ X0 @ X1))
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['3', '10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         ((r1_tarski @ (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ X1)) @ 
% 0.19/0.45           (k5_relat_1 @ X0 @ X1))
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X1))),
% 0.19/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.45  thf(t122_relat_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) =>
% 0.19/0.45       ( ![C:$i]:
% 0.19/0.45         ( ( v1_relat_1 @ C ) =>
% 0.19/0.45           ( r1_tarski @
% 0.19/0.45             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) @ 
% 0.19/0.45             ( k5_relat_1 @ B @ C ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( v1_relat_1 @ B ) =>
% 0.19/0.45          ( ![C:$i]:
% 0.19/0.45            ( ( v1_relat_1 @ C ) =>
% 0.19/0.45              ( r1_tarski @
% 0.19/0.45                ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) @ 
% 0.19/0.45                ( k5_relat_1 @ B @ C ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t122_relat_1])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C)) @ 
% 0.19/0.45          (k5_relat_1 @ sk_B @ sk_C))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('14', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.45  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('17', plain, ($false),
% 0.19/0.45      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
