%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WOzi4Nrbgj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  449 ( 590 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WOzi4Nrbgj
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:38:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 39 iterations in 0.045s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(d3_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf(t143_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.51         ( ?[D:$i]:
% 0.22/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.22/0.51          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf(t156_relat_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.51         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ C ) =>
% 0.22/0.51          ( ( r1_tarski @ A @ B ) =>
% 0.22/0.51            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.22/0.51  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.51          | (r2_hidden @ X0 @ X2)
% 0.22/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (sk_D @ X0 @ sk_A @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.22/0.51          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ (k1_relat_1 @ X7))
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.51             (k1_relat_1 @ X1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X5 @ X6) @ X6) @ X7)
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (k4_tarski @ 
% 0.22/0.51              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.51              (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.51             X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X7)
% 0.22/0.51          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X7))
% 0.22/0.51          | (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.22/0.51             (k9_relat_1 @ X0 @ X3))
% 0.22/0.51          | ~ (r2_hidden @ 
% 0.22/0.51               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.22/0.51               (k1_relat_1 @ X0))
% 0.22/0.51          | ~ (r2_hidden @ 
% 0.22/0.51               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ 
% 0.22/0.51             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3)
% 0.22/0.51          | ~ (r2_hidden @ 
% 0.22/0.51               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.22/0.51               (k1_relat_1 @ X0))
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.22/0.51             (k9_relat_1 @ X0 @ X3))
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.22/0.51             (k9_relat_1 @ X0 @ X3))
% 0.22/0.51          | ~ (r2_hidden @ 
% 0.22/0.51               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ 
% 0.22/0.51             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.22/0.51             (k9_relat_1 @ X0 @ X3))
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.22/0.51             (k9_relat_1 @ X0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.22/0.51           (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.22/0.51          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ($false), inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
