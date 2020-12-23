%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsA6uSvIKN

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:53 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 112 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  563 (1013 expanded)
%              Number of equality atoms :   43 (  71 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X5 @ X4 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X23 @ X29 )
      | ( X29
       != ( k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X23 @ ( k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X20 @ X21 @ X16 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X34 ) @ X35 )
      | ~ ( r2_hidden @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X36: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X41 @ X40 ) @ X42 )
        = ( k1_funct_1 @ X40 @ ( k1_funct_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X39: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','19'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('29',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X44 ) @ X43 )
        = X43 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('30',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_A )
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsA6uSvIKN
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 291 iterations in 0.228s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.51/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.51/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.51/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.51/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.51/0.71  thf(t38_funct_1, conjecture,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.71       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.51/0.71         ( ( k1_funct_1 @ C @ A ) =
% 0.51/0.71           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.71        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.71          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.51/0.71            ( ( k1_funct_1 @ C @ A ) =
% 0.51/0.71              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.51/0.71  thf('0', plain,
% 0.51/0.71      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(t71_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.51/0.71  thf('1', plain,
% 0.51/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.51/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.51/0.71  thf(t102_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.51/0.71  thf('2', plain,
% 0.51/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X6 @ X5 @ X4) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.51/0.71      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.51/0.71  thf(t70_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      (![X7 : $i, X8 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.51/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.71  thf('4', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.51/0.71  thf(t72_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.51/0.71  thf('6', plain,
% 0.51/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.51/0.71           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.51/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.71  thf(d3_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.71     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.51/0.71       ( ![G:$i]:
% 0.51/0.71         ( ( r2_hidden @ G @ F ) <=>
% 0.51/0.71           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.51/0.71                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.51/0.71  thf(zf_stmt_2, axiom,
% 0.51/0.71    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.51/0.71     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.51/0.71       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.51/0.71         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_3, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.71     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.51/0.71       ( ![G:$i]:
% 0.51/0.71         ( ( r2_hidden @ G @ F ) <=>
% 0.51/0.71           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.51/0.71  thf('7', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.51/0.71         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.51/0.71          | (r2_hidden @ X23 @ X29)
% 0.51/0.71          | ((X29) != (k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.71  thf('8', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.71         ((r2_hidden @ X23 @ (k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24))
% 0.51/0.71          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.51/0.71      inference('simplify', [status(thm)], ['7'])).
% 0.51/0.71  thf('9', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.71         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.51/0.71          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.51/0.71      inference('sup+', [status(thm)], ['6', '8'])).
% 0.51/0.71  thf('10', plain,
% 0.51/0.71      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         (((X17) != (X16))
% 0.51/0.71          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X16))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('11', plain,
% 0.51/0.71      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X20 @ X21 @ X16)),
% 0.51/0.71      inference('simplify', [status(thm)], ['10'])).
% 0.51/0.71  thf('12', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.71         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '11'])).
% 0.51/0.71  thf('13', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['5', '12'])).
% 0.51/0.71  thf(t4_setfam_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      (![X34 : $i, X35 : $i]:
% 0.51/0.71         ((r1_tarski @ (k1_setfam_1 @ X34) @ X35) | ~ (r2_hidden @ X35 @ X34))),
% 0.51/0.71      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.51/0.71  thf('15', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.51/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.51/0.71  thf(t12_setfam_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.71  thf('16', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i]:
% 0.51/0.71         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.51/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.51/0.71  thf(d3_tarski, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.71  thf('18', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.71          | (r2_hidden @ X0 @ X2)
% 0.51/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.71  thf('19', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.71  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.51/0.71      inference('sup-', [status(thm)], ['0', '19'])).
% 0.51/0.71  thf(t71_relat_1, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.51/0.71       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.51/0.71  thf('21', plain, (![X36 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X36)) = (X36))),
% 0.51/0.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.71  thf(t23_funct_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.71       ( ![C:$i]:
% 0.51/0.71         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.71           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.71             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.51/0.71               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X40)
% 0.51/0.71          | ~ (v1_funct_1 @ X40)
% 0.51/0.71          | ((k1_funct_1 @ (k5_relat_1 @ X41 @ X40) @ X42)
% 0.51/0.71              = (k1_funct_1 @ X40 @ (k1_funct_1 @ X41 @ X42)))
% 0.51/0.71          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ X41))
% 0.51/0.71          | ~ (v1_funct_1 @ X41)
% 0.51/0.71          | ~ (v1_relat_1 @ X41))),
% 0.51/0.71      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X1 @ X0)
% 0.51/0.71          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.51/0.71          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.51/0.71          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.51/0.71              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.51/0.71          | ~ (v1_funct_1 @ X2)
% 0.51/0.71          | ~ (v1_relat_1 @ X2))),
% 0.51/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.71  thf(fc3_funct_1, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.51/0.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.51/0.71  thf('24', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.51/0.71      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.71  thf('25', plain, (![X39 : $i]: (v1_funct_1 @ (k6_relat_1 @ X39))),
% 0.51/0.71      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.71  thf('26', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X1 @ X0)
% 0.51/0.71          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.51/0.71              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.51/0.71          | ~ (v1_funct_1 @ X2)
% 0.51/0.71          | ~ (v1_relat_1 @ X2))),
% 0.51/0.71      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X0)
% 0.51/0.71          | ~ (v1_funct_1 @ X0)
% 0.51/0.71          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.51/0.71              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['20', '26'])).
% 0.51/0.71  thf('28', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.51/0.71      inference('sup-', [status(thm)], ['0', '19'])).
% 0.51/0.71  thf(t35_funct_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r2_hidden @ A @ B ) =>
% 0.51/0.71       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.51/0.71  thf('29', plain,
% 0.51/0.71      (![X43 : $i, X44 : $i]:
% 0.51/0.71         (((k1_funct_1 @ (k6_relat_1 @ X44) @ X43) = (X43))
% 0.51/0.71          | ~ (r2_hidden @ X43 @ X44))),
% 0.51/0.71      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.51/0.71  thf('30', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X0)
% 0.51/0.71          | ~ (v1_funct_1 @ X0)
% 0.51/0.71          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.51/0.71              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.51/0.71      inference('demod', [status(thm)], ['27', '30'])).
% 0.51/0.71  thf('32', plain,
% 0.51/0.71      (((k1_funct_1 @ sk_C_1 @ sk_A)
% 0.51/0.71         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C_1) @ sk_A))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('33', plain,
% 0.51/0.71      ((((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.51/0.71        | ~ (v1_relat_1 @ sk_C_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.71  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('36', plain,
% 0.51/0.71      (((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.51/0.71  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
