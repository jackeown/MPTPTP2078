%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D1cDek9l1Q

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:17 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  640 (1220 expanded)
%              Number of equality atoms :   52 (  92 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t168_funct_1])).

thf('2',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = X1 )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = ( k1_tarski @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ X0 )
       != X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('26',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D1cDek9l1Q
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.72/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.91  % Solved by: fo/fo7.sh
% 0.72/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.91  % done 706 iterations in 0.476s
% 0.72/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.91  % SZS output start Refutation
% 0.72/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.72/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.91  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.72/0.91  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.72/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.72/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.72/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.91  thf(d16_relat_1, axiom,
% 0.72/0.91    (![A:$i]:
% 0.72/0.91     ( ( v1_relat_1 @ A ) =>
% 0.72/0.91       ( ![B:$i]:
% 0.72/0.91         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.72/0.91  thf('0', plain,
% 0.72/0.91      (![X8 : $i, X9 : $i]:
% 0.72/0.91         (((k11_relat_1 @ X8 @ X9) = (k9_relat_1 @ X8 @ (k1_tarski @ X9)))
% 0.72/0.91          | ~ (v1_relat_1 @ X8))),
% 0.72/0.91      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.72/0.91  thf(t148_relat_1, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( v1_relat_1 @ B ) =>
% 0.72/0.91       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.72/0.91  thf('1', plain,
% 0.72/0.91      (![X10 : $i, X11 : $i]:
% 0.72/0.91         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.72/0.91          | ~ (v1_relat_1 @ X10))),
% 0.72/0.91      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.72/0.91  thf(t168_funct_1, conjecture,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.72/0.91       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.72/0.91         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.72/0.91           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.72/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.91    (~( ![A:$i,B:$i]:
% 0.72/0.91        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.72/0.91          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.72/0.91            ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.72/0.91              ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.72/0.91    inference('cnf.neg', [status(esa)], [t168_funct_1])).
% 0.72/0.91  thf('2', plain,
% 0.72/0.91      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.72/0.91         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('3', plain,
% 0.72/0.91      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.72/0.91          != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.72/0.91        | ~ (v1_relat_1 @ sk_B))),
% 0.72/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.91  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('5', plain,
% 0.72/0.91      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.72/0.91         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.72/0.91  thf(d1_tarski, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.72/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.72/0.91  thf('6', plain,
% 0.72/0.91      (![X0 : $i, X4 : $i]:
% 0.72/0.91         (((X4) = (k1_tarski @ X0))
% 0.72/0.91          | ((sk_C @ X4 @ X0) = (X0))
% 0.72/0.91          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.72/0.91      inference('cnf', [status(esa)], [d1_tarski])).
% 0.72/0.91  thf(t204_relat_1, axiom,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ( v1_relat_1 @ C ) =>
% 0.72/0.91       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.72/0.91         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.72/0.91  thf('7', plain,
% 0.72/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.72/0.91         (~ (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.72/0.91          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.72/0.91          | ~ (v1_relat_1 @ X13))),
% 0.72/0.91      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.72/0.91  thf('8', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.72/0.91          | ~ (v1_relat_1 @ X1)
% 0.72/0.91          | (r2_hidden @ 
% 0.72/0.91             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1))),
% 0.72/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.72/0.91  thf(t8_funct_1, axiom,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.72/0.91       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.72/0.91         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.72/0.91           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.72/0.91  thf('9', plain,
% 0.72/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.91         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.72/0.91          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.72/0.91          | ~ (v1_funct_1 @ X16)
% 0.72/0.91          | ~ (v1_relat_1 @ X16))),
% 0.72/0.91      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.72/0.91  thf('10', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (~ (v1_relat_1 @ X0)
% 0.72/0.91          | ((k11_relat_1 @ X0 @ X2) = (k1_tarski @ X1))
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (X1))
% 0.72/0.91          | ~ (v1_relat_1 @ X0)
% 0.72/0.91          | ~ (v1_funct_1 @ X0)
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (k1_funct_1 @ X0 @ X2)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.91  thf('11', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (k1_funct_1 @ X0 @ X2))
% 0.72/0.91          | ~ (v1_funct_1 @ X0)
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (X1))
% 0.72/0.91          | ((k11_relat_1 @ X0 @ X2) = (k1_tarski @ X1))
% 0.72/0.91          | ~ (v1_relat_1 @ X0))),
% 0.72/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.72/0.91  thf('12', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (((k1_funct_1 @ X1 @ X0) != (X2))
% 0.72/0.91          | ~ (v1_relat_1 @ X1)
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.72/0.91          | ~ (v1_funct_1 @ X1))),
% 0.72/0.91      inference('eq_fact', [status(thm)], ['11'])).
% 0.72/0.91  thf('13', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (~ (v1_funct_1 @ X1)
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 0.72/0.91              = (k1_funct_1 @ X1 @ X0))
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 0.72/0.91          | ~ (v1_relat_1 @ X1))),
% 0.72/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.72/0.91  thf('14', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('15', plain,
% 0.72/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.91         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.72/0.91          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.72/0.91          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.72/0.91          | ~ (v1_funct_1 @ X16)
% 0.72/0.91          | ~ (v1_relat_1 @ X16))),
% 0.72/0.91      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.72/0.91  thf('16', plain,
% 0.72/0.91      (![X15 : $i, X16 : $i]:
% 0.72/0.91         (~ (v1_relat_1 @ X16)
% 0.72/0.91          | ~ (v1_funct_1 @ X16)
% 0.72/0.91          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.72/0.91          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.72/0.91      inference('simplify', [status(thm)], ['15'])).
% 0.72/0.91  thf('17', plain,
% 0.72/0.91      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.72/0.91        | ~ (v1_funct_1 @ sk_B)
% 0.72/0.91        | ~ (v1_relat_1 @ sk_B))),
% 0.72/0.91      inference('sup-', [status(thm)], ['14', '16'])).
% 0.72/0.91  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('20', plain,
% 0.72/0.91      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.72/0.91      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.72/0.91  thf('21', plain,
% 0.72/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.72/0.91         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.72/0.91          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.72/0.91          | ~ (v1_relat_1 @ X13))),
% 0.72/0.91      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.72/0.91  thf('22', plain,
% 0.72/0.91      ((~ (v1_relat_1 @ sk_B)
% 0.72/0.91        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.91  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('24', plain,
% 0.72/0.91      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.72/0.91  thf('25', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (~ (v1_funct_1 @ X1)
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 0.72/0.91              = (k1_funct_1 @ X1 @ X0))
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 0.72/0.91          | ~ (v1_relat_1 @ X1))),
% 0.72/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.72/0.91  thf('26', plain,
% 0.72/0.91      (![X0 : $i, X4 : $i]:
% 0.72/0.91         (((X4) = (k1_tarski @ X0))
% 0.72/0.91          | ((sk_C @ X4 @ X0) != (X0))
% 0.72/0.91          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.72/0.91      inference('cnf', [status(esa)], [d1_tarski])).
% 0.72/0.91  thf('27', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k11_relat_1 @ X1 @ X0))
% 0.72/0.91          | ~ (v1_relat_1 @ X1)
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 0.72/0.91          | ~ (v1_funct_1 @ X1)
% 0.72/0.91          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 0.72/0.91              != (k1_funct_1 @ X1 @ X0))
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0))))),
% 0.72/0.91      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.91  thf('28', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 0.72/0.91            != (k1_funct_1 @ X1 @ X0))
% 0.72/0.91          | ~ (v1_funct_1 @ X1)
% 0.72/0.91          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 0.72/0.91          | ~ (v1_relat_1 @ X1)
% 0.72/0.91          | ~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k11_relat_1 @ X1 @ X0)))),
% 0.72/0.91      inference('simplify', [status(thm)], ['27'])).
% 0.72/0.91  thf('29', plain,
% 0.72/0.91      ((~ (v1_relat_1 @ sk_B)
% 0.72/0.91        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.72/0.91            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.72/0.91        | ~ (v1_funct_1 @ sk_B)
% 0.72/0.91        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.72/0.91            != (k1_funct_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['24', '28'])).
% 0.72/0.91  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('32', plain,
% 0.72/0.91      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.72/0.91        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.72/0.91            != (k1_funct_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.72/0.91  thf('33', plain,
% 0.72/0.91      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.72/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.72/0.91        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.72/0.91            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.72/0.91        | ~ (v1_funct_1 @ sk_B)
% 0.72/0.91        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.72/0.91            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.72/0.91      inference('sup-', [status(thm)], ['13', '32'])).
% 0.72/0.91  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('36', plain,
% 0.72/0.91      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.72/0.91        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.72/0.91            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.72/0.91        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.72/0.91            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.72/0.91      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.72/0.91  thf('37', plain,
% 0.72/0.91      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.72/0.91      inference('simplify', [status(thm)], ['36'])).
% 0.72/0.91  thf('38', plain,
% 0.72/0.91      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k11_relat_1 @ sk_B @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['5', '37'])).
% 0.72/0.91  thf('39', plain,
% 0.72/0.91      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 0.72/0.91        | ~ (v1_relat_1 @ sk_B))),
% 0.72/0.91      inference('sup-', [status(thm)], ['0', '38'])).
% 0.72/0.91  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('41', plain,
% 0.72/0.91      (((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))),
% 0.72/0.91      inference('demod', [status(thm)], ['39', '40'])).
% 0.72/0.91  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.72/0.91  
% 0.72/0.91  % SZS output end Refutation
% 0.72/0.91  
% 0.72/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
