%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GHpSf8nldH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:22 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   60 (  80 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  603 ( 859 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k10_relat_1 @ X21 @ ( k10_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D @ X15 @ X13 @ X14 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X25 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k10_relat_1 @ X21 @ ( k10_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k10_relat_1 @ X19 @ X17 ) @ ( k10_relat_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t182_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t182_relat_1])).

thf('32',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GHpSf8nldH
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:39:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.37  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 115 iterations in 0.115s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.59  thf(t169_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X16 : $i]:
% 0.38/0.59         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 0.38/0.59          | ~ (v1_relat_1 @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.59  thf(dt_k5_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.38/0.59       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X10)
% 0.38/0.59          | ~ (v1_relat_1 @ X11)
% 0.38/0.59          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.59  thf(t181_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ B ) =>
% 0.38/0.59       ( ![C:$i]:
% 0.38/0.59         ( ( v1_relat_1 @ C ) =>
% 0.38/0.59           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.38/0.59             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X20)
% 0.38/0.59          | ((k10_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.38/0.59              = (k10_relat_1 @ X21 @ (k10_relat_1 @ X20 @ X22)))
% 0.38/0.59          | ~ (v1_relat_1 @ X21))),
% 0.38/0.59      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.38/0.59  thf(d3_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf(t166_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ C ) =>
% 0.38/0.59       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.38/0.59         ( ?[D:$i]:
% 0.38/0.59           ( ( r2_hidden @ D @ B ) & 
% 0.38/0.59             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.38/0.59             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.38/0.59          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D @ X15 @ X13 @ X14)) @ X15)
% 0.38/0.59          | ~ (v1_relat_1 @ X15))),
% 0.38/0.59      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.38/0.59             X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(t20_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ C ) =>
% 0.38/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.38/0.59         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.59           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.59         (~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X25)
% 0.38/0.59          | (r2_hidden @ X23 @ (k1_relat_1 @ X25))
% 0.38/0.59          | ~ (v1_relat_1 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.38/0.59             (k1_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.38/0.59           (k1_relat_1 @ X0))
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59           (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.59          | ~ (v1_relat_1 @ X2)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['2', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.38/0.59             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '12'])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ X0 @ X2)) @ 
% 0.38/0.59           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.38/0.59           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['0', '14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.38/0.59             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X10)
% 0.38/0.59          | ~ (v1_relat_1 @ X11)
% 0.38/0.59          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X20)
% 0.38/0.59          | ((k10_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.38/0.59              = (k10_relat_1 @ X21 @ (k10_relat_1 @ X20 @ X22)))
% 0.38/0.59          | ~ (v1_relat_1 @ X21))),
% 0.38/0.59      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X16 : $i]:
% 0.38/0.59         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 0.38/0.59          | ~ (v1_relat_1 @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k10_relat_1 @ X1 @ 
% 0.38/0.59            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.38/0.59            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ((k10_relat_1 @ X1 @ 
% 0.38/0.59              (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.38/0.59              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '20'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k10_relat_1 @ X1 @ 
% 0.38/0.59            (k10_relat_1 @ X0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.38/0.59            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.59  thf(t178_relat_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ C ) =>
% 0.38/0.59       ( ( r1_tarski @ A @ B ) =>
% 0.38/0.59         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.59         (~ (r1_tarski @ X17 @ X18)
% 0.38/0.59          | ~ (v1_relat_1 @ X19)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X19 @ X17) @ (k10_relat_1 @ X19 @ X18)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.38/0.59             (k10_relat_1 @ X2 @ (k1_relat_1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['22', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.38/0.59             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X4 : $i, X6 : $i]:
% 0.38/0.59         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.38/0.59               (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ((k10_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.59              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ((k10_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.59              = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '29'])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k10_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.59            = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.59  thf(t182_relat_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( v1_relat_1 @ B ) =>
% 0.38/0.59           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.59             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( v1_relat_1 @ A ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( v1_relat_1 @ B ) =>
% 0.38/0.59              ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.59                ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t182_relat_1])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.38/0.59         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.38/0.59          != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.38/0.59         != (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.38/0.59  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
