%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uulDGtZuxj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  57 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  143 ( 599 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t218_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X1 )
      | ( v5_relat_1 @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t218_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['13','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uulDGtZuxj
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 15 iterations in 0.009s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(t47_ordinal1, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.45       ( ![C:$i]:
% 0.21/0.45         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.45             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.21/0.45           ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.21/0.45             ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ( r1_tarski @ A @ B ) =>
% 0.21/0.45          ( ![C:$i]:
% 0.21/0.45            ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.45                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) =>
% 0.21/0.45              ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) & 
% 0.21/0.45                ( v1_funct_1 @ C ) & ( v5_ordinal1 @ C ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t47_ordinal1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.45        | ~ (v5_relat_1 @ sk_C @ sk_B)
% 0.21/0.45        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.45        | ~ (v5_ordinal1 @ sk_C))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((~ (v5_relat_1 @ sk_C @ sk_B)) <= (~ ((v5_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.45      inference('split', [status(esa)], ['0'])).
% 0.21/0.45  thf('2', plain, ((v5_ordinal1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('3', plain, ((~ (v5_ordinal1 @ sk_C)) <= (~ ((v5_ordinal1 @ sk_C)))),
% 0.21/0.45      inference('split', [status(esa)], ['0'])).
% 0.21/0.45  thf('4', plain, (((v5_ordinal1 @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.45  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('6', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.21/0.45      inference('split', [status(esa)], ['0'])).
% 0.21/0.45  thf('7', plain, (((v1_funct_1 @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('9', plain, ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_relat_1 @ sk_C)))),
% 0.21/0.45      inference('split', [status(esa)], ['0'])).
% 0.21/0.45  thf('10', plain, (((v1_relat_1 @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (~ ((v5_relat_1 @ sk_C @ sk_B)) | ~ ((v1_relat_1 @ sk_C)) | 
% 0.21/0.45       ~ ((v1_funct_1 @ sk_C)) | ~ ((v5_ordinal1 @ sk_C))),
% 0.21/0.45      inference('split', [status(esa)], ['0'])).
% 0.21/0.45  thf('12', plain, (~ ((v5_relat_1 @ sk_C @ sk_B))),
% 0.21/0.45      inference('sat_resolution*', [status(thm)], ['4', '7', '10', '11'])).
% 0.21/0.45  thf('13', plain, (~ (v5_relat_1 @ sk_C @ sk_B)),
% 0.21/0.45      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.21/0.45  thf('14', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t218_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.45       ( ![C:$i]:
% 0.21/0.45         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.21/0.45           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X0)
% 0.21/0.45          | ~ (v5_relat_1 @ X0 @ X1)
% 0.21/0.45          | (v5_relat_1 @ X0 @ X2)
% 0.21/0.45          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [t218_relat_1])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((v5_relat_1 @ X0 @ sk_B)
% 0.21/0.45          | ~ (v5_relat_1 @ X0 @ sk_A)
% 0.21/0.45          | ~ (v1_relat_1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain, ((~ (v1_relat_1 @ sk_C) | (v5_relat_1 @ sk_C @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.45  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('20', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.21/0.45      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('21', plain, ($false), inference('demod', [status(thm)], ['13', '20'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
