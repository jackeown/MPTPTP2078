%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWuTKy3Nnc

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 106 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  551 (1190 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X13 ) @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X13 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( X12
       != ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X14 ) @ X10 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X14 ) @ X10 )
      | ( r2_hidden @ X14 @ ( k10_relat_1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_A ) ) @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_A ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWuTKy3Nnc
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:37:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 122 iterations in 0.057s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.53  thf(t157_funct_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.22/0.53           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.53         ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.53        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.22/0.53              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.53            ( r1_tarski @ A @ B ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.22/0.53  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X1 : $i, X3 : $i]:
% 0.22/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf(t152_funct_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ B ) =>
% 0.22/0.53         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X17)
% 0.22/0.53          | (r1_tarski @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X18)) @ X18)
% 0.22/0.53          | ~ (v1_funct_1 @ X17)
% 0.22/0.53          | ~ (v1_relat_1 @ X17))),
% 0.22/0.53      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.22/0.53  thf('3', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t146_funct_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.22/0.53          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)))
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.53        | (r1_tarski @ sk_A @ 
% 0.22/0.53           (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      ((r1_tarski @ sk_A @ 
% 0.22/0.53        (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X4 : $i, X6 : $i]:
% 0.22/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((~ (r1_tarski @ (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.22/0.53           sk_A)
% 0.22/0.53        | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.53        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53        | ~ (v2_funct_1 @ sk_C_1)
% 0.22/0.53        | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '9'])).
% 0.22/0.53  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.22/0.53  thf(d13_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ![B:$i,C:$i]:
% 0.22/0.53         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.22/0.53           ( ![D:$i]:
% 0.22/0.53             ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.53               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.53                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.53         (((X12) != (k10_relat_1 @ X11 @ X10))
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ X11 @ X13) @ X10)
% 0.22/0.53          | ~ (r2_hidden @ X13 @ X12)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ X13 @ (k10_relat_1 @ X11 @ X10))
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ X11 @ X13) @ X10))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.22/0.53             (k9_relat_1 @ sk_C_1 @ sk_A))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.53  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.22/0.53             (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_A)) @ 
% 0.22/0.53             (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_A)) @ 
% 0.22/0.53             (k9_relat_1 @ sk_C_1 @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X1 : $i, X3 : $i]:
% 0.22/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('27', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.22/0.53         (((X12) != (k10_relat_1 @ X11 @ X10))
% 0.22/0.53          | (r2_hidden @ X14 @ X12)
% 0.22/0.53          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X14) @ X10)
% 0.22/0.53          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X11))
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X11))
% 0.22/0.53          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X14) @ X10)
% 0.22/0.53          | (r2_hidden @ X14 @ (k10_relat_1 @ X11 @ X10)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k10_relat_1 @ sk_C_1 @ X1))
% 0.22/0.53          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_A)) @ X1)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '32'])).
% 0.22/0.53  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k10_relat_1 @ sk_C_1 @ X1))
% 0.22/0.53          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_A)) @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.22/0.53             (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)))
% 0.22/0.53          | (r1_tarski @ sk_A @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['25', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.22/0.53           (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)))
% 0.22/0.53          | (r1_tarski @ sk_A @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X17)
% 0.22/0.53          | (r1_tarski @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X18)) @ X18)
% 0.22/0.53          | ~ (v1_funct_1 @ X17)
% 0.22/0.53          | ~ (v1_relat_1 @ X17))),
% 0.22/0.53      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X1)
% 0.22/0.53          | ~ (v1_funct_1 @ X1)
% 0.22/0.53          | ~ (v2_funct_1 @ X1)
% 0.22/0.53          | (r2_hidden @ X2 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0)
% 0.22/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.22/0.53          | ~ (v2_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '41'])).
% 0.22/0.53  thf('43', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (![X1 : $i, X3 : $i]:
% 0.22/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('48', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.53  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
