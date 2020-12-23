%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnysQX4pP6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:05 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   64 (  80 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  447 ( 713 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k9_relat_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnysQX4pP6
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 323 iterations in 0.158s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(t125_funct_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.61       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.61         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.61          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.61            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.41/0.61  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t3_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf(t4_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.41/0.61          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.41/0.61          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.41/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X1 @ X0)
% 0.41/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.41/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X0 @ X1)
% 0.41/0.61          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.41/0.61          | (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '10'])).
% 0.41/0.61  thf(t151_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.61         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ (k1_relat_1 @ X16) @ X17)
% 0.41/0.61          | ((k9_relat_1 @ X16 @ X17) = (k1_xboole_0))
% 0.41/0.61          | ~ (v1_relat_1 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X0)
% 0.41/0.61          | ((k9_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf(t121_funct_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.61       ( ( v2_funct_1 @ C ) =>
% 0.41/0.61         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.41/0.61           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (v2_funct_1 @ X18)
% 0.41/0.61          | ((k9_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.41/0.61              = (k3_xboole_0 @ (k9_relat_1 @ X18 @ X19) @ 
% 0.41/0.61                 (k9_relat_1 @ X18 @ X20)))
% 0.41/0.61          | ~ (v1_funct_1 @ X18)
% 0.41/0.61          | ~ (v1_relat_1 @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X4 @ X5)
% 0.41/0.61          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X4 @ X5)
% 0.41/0.61          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.41/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X1 @ X0)
% 0.41/0.61          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.41/0.61          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X1 @ X0)
% 0.41/0.61          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.61          | (r1_xboole_0 @ X1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.61          | (r1_xboole_0 @ X1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.61             (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))
% 0.41/0.61          | ~ (v1_relat_1 @ X2)
% 0.41/0.61          | ~ (v1_funct_1 @ X2)
% 0.41/0.61          | ~ (v2_funct_1 @ X2)
% 0.41/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['14', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.41/0.61             (k3_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))
% 0.41/0.61          | ~ (v1_relat_1 @ X0)
% 0.41/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.41/0.61          | ~ (v2_funct_1 @ X0)
% 0.41/0.61          | ~ (v1_funct_1 @ X0)
% 0.41/0.61          | ~ (v1_relat_1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '21'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf(t2_boole, axiom,
% 0.41/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.41/0.61          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf(t3_boole, axiom,
% 0.41/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.61  thf('27', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.61  thf(t79_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.41/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.41/0.61  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.41/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('30', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '29'])).
% 0.41/0.61  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.41/0.61      inference('sup-', [status(thm)], ['23', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X0)
% 0.41/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.41/0.61          | ~ (v2_funct_1 @ X0)
% 0.41/0.61          | ~ (v1_funct_1 @ X0)
% 0.41/0.61          | ~ (v1_relat_1 @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['22', '31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_funct_1 @ X0)
% 0.41/0.61          | ~ (v2_funct_1 @ X0)
% 0.41/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.41/0.61          | ~ (v1_relat_1 @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['32'])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.41/0.61          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_2)
% 0.41/0.61        | ~ (v2_funct_1 @ sk_C_2)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C_2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('36', plain, ((v1_relat_1 @ sk_C_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('37', plain, ((v2_funct_1 @ sk_C_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('38', plain, ((v1_funct_1 @ sk_C_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('39', plain, ($false),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
