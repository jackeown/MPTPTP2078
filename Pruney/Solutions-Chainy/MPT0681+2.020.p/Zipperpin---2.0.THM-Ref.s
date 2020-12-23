%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q7jYJYU3ny

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:05 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   64 (  78 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 ( 691 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 )
      | ( ( k9_relat_1 @ X43 @ X44 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k9_relat_1 @ X45 @ ( k3_xboole_0 @ X46 @ X47 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X45 @ X46 ) @ ( k9_relat_1 @ X45 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('17',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k9_relat_1 @ X45 @ ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X45 @ X46 ) @ ( k9_relat_1 @ X45 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k5_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
        = ( k5_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
        = ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
        = ( k9_relat_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ sk_A )
       != ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['32','33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q7jYJYU3ny
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 232 iterations in 0.151s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(t125_funct_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.61       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.61         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.61          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.61            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.40/0.61  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf(t4_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.40/0.61          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.61  thf(t12_setfam_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X41 : $i, X42 : $i]:
% 0.40/0.61         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.40/0.61          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 0.40/0.61          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (r1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)) @ X0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.40/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.40/0.61          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.61          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.61          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['7', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (r1_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['6', '12'])).
% 0.40/0.61  thf(t151_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.61         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         (~ (r1_xboole_0 @ (k1_relat_1 @ X43) @ X44)
% 0.40/0.61          | ((k9_relat_1 @ X43 @ X44) = (k1_xboole_0))
% 0.40/0.61          | ~ (v1_relat_1 @ X43))),
% 0.40/0.61      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ((k9_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.40/0.61              = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf(t121_funct_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.61       ( ( v2_funct_1 @ C ) =>
% 0.40/0.61         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.40/0.61           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X45)
% 0.40/0.61          | ((k9_relat_1 @ X45 @ (k3_xboole_0 @ X46 @ X47))
% 0.40/0.61              = (k3_xboole_0 @ (k9_relat_1 @ X45 @ X46) @ 
% 0.40/0.61                 (k9_relat_1 @ X45 @ X47)))
% 0.40/0.61          | ~ (v1_funct_1 @ X45)
% 0.40/0.61          | ~ (v1_relat_1 @ X45))),
% 0.40/0.61      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X41 : $i, X42 : $i]:
% 0.40/0.61         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X41 : $i, X42 : $i]:
% 0.40/0.61         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X45)
% 0.40/0.61          | ((k9_relat_1 @ X45 @ (k1_setfam_1 @ (k2_tarski @ X46 @ X47)))
% 0.40/0.61              = (k1_setfam_1 @ 
% 0.40/0.61                 (k2_tarski @ (k9_relat_1 @ X45 @ X46) @ 
% 0.40/0.61                  (k9_relat_1 @ X45 @ X47))))
% 0.40/0.61          | ~ (v1_funct_1 @ X45)
% 0.40/0.61          | ~ (v1_relat_1 @ X45))),
% 0.40/0.61      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.40/0.61  thf(t100_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X8 @ X9)
% 0.40/0.61           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X41 : $i, X42 : $i]:
% 0.40/0.61         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X8 @ X9)
% 0.40/0.61           = (k5_xboole_0 @ X8 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9))))),
% 0.40/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (((k4_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0))
% 0.40/0.61            = (k5_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.40/0.61               (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))
% 0.40/0.61          | ~ (v1_relat_1 @ X2)
% 0.40/0.61          | ~ (v1_funct_1 @ X2)
% 0.40/0.61          | ~ (v2_funct_1 @ X2))),
% 0.40/0.61      inference('sup+', [status(thm)], ['19', '22'])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k4_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.40/0.61            = (k5_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ k1_xboole_0))
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v2_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['15', '23'])).
% 0.40/0.61  thf(t5_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.61  thf('25', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.40/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k4_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.40/0.61            = (k9_relat_1 @ X0 @ sk_A))
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v2_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v2_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ((k4_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.40/0.61              = (k9_relat_1 @ X0 @ sk_A)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.61  thf(t83_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X11 : $i, X13 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k9_relat_1 @ X0 @ sk_A) != (k9_relat_1 @ X0 @ sk_A))
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v2_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_1 @ X0)
% 0.40/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.40/0.61          | ~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v2_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.40/0.61          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ sk_C_2)
% 0.40/0.61        | ~ (v2_funct_1 @ sk_C_2)
% 0.40/0.61        | ~ (v1_funct_1 @ sk_C_2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('33', plain, ((v1_relat_1 @ sk_C_2)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('34', plain, ((v2_funct_1 @ sk_C_2)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('35', plain, ((v1_funct_1 @ sk_C_2)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('36', plain, ($false),
% 0.40/0.61      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
