%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1piMFXCAI4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 140 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  553 (1062 expanded)
%              Number of equality atoms :   71 ( 142 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('0',plain,(
    ! [X61: $i,X63: $i,X64: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X61 @ X63 ) @ X64 )
        = ( k1_tarski @ X61 ) )
      | ( X61 != X63 )
      | ( r2_hidden @ X61 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('1',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r2_hidden @ X63 @ X64 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X63 @ X63 ) @ X64 )
        = ( k1_tarski @ X63 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r2_hidden @ X63 @ X64 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X63 ) @ X64 )
        = ( k1_tarski @ X63 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X65: $i,X67: $i,X68: $i] :
      ( ( r1_tarski @ X67 @ ( k2_tarski @ X65 @ X68 ) )
      | ( X67
       != ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,(
    ! [X65: $i,X68: $i] :
      ( r1_tarski @ ( k1_tarski @ X65 ) @ ( k2_tarski @ X65 @ X68 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X65: $i,X67: $i,X68: $i] :
      ( ( r1_tarski @ X67 @ ( k2_tarski @ X65 @ X68 ) )
      | ( X67 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('20',plain,(
    ! [X65: $i,X68: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X65 @ X68 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34','35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','37'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','38'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('40',plain,(
    ! [X69: $i,X70: $i] :
      ( ( X70 != X69 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X70 ) @ ( k1_tarski @ X69 ) )
       != ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('41',plain,(
    ! [X69: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X69 ) @ ( k1_tarski @ X69 ) )
     != ( k1_tarski @ X69 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X69: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X69 ) @ ( k1_tarski @ X69 ) )
     != ( k1_tarski @ X69 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34','35','36'])).

thf('45',plain,(
    ! [X69: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X69 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['39','45'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X25 )
      | ( X27 = X26 )
      | ( X27 = X23 )
      | ( X25
       != ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('48',plain,(
    ! [X23: $i,X26: $i,X27: $i] :
      ( ( X27 = X23 )
      | ( X27 = X26 )
      | ~ ( r2_hidden @ X27 @ ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1piMFXCAI4
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:23 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 248 iterations in 0.135s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(l38_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.59       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.41/0.59         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X61 : $i, X63 : $i, X64 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ (k2_tarski @ X61 @ X63) @ X64) = (k1_tarski @ X61))
% 0.41/0.59          | ((X61) != (X63))
% 0.41/0.59          | (r2_hidden @ X61 @ X64))),
% 0.41/0.59      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X63 : $i, X64 : $i]:
% 0.41/0.59         ((r2_hidden @ X63 @ X64)
% 0.41/0.59          | ((k4_xboole_0 @ (k2_tarski @ X63 @ X63) @ X64) = (k1_tarski @ X63)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.41/0.59  thf(t69_enumset1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.59  thf('2', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X63 : $i, X64 : $i]:
% 0.41/0.59         ((r2_hidden @ X63 @ X64)
% 0.41/0.59          | ((k4_xboole_0 @ (k1_tarski @ X63) @ X64) = (k1_tarski @ X63)))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf(l45_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.41/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.41/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X65 : $i, X67 : $i, X68 : $i]:
% 0.41/0.59         ((r1_tarski @ X67 @ (k2_tarski @ X65 @ X68))
% 0.41/0.59          | ((X67) != (k1_tarski @ X65)))),
% 0.41/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X65 : $i, X68 : $i]:
% 0.41/0.59         (r1_tarski @ (k1_tarski @ X65) @ (k2_tarski @ X65 @ X68))),
% 0.41/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.59  thf(t28_zfmisc_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.41/0.59          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.41/0.59             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t28_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.41/0.59         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf(t18_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.59         ((r1_tarski @ X12 @ X13)
% 0.41/0.59          | ~ (r1_tarski @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.41/0.59          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['5', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.41/0.59         = (k1_tarski @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf(t100_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.41/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.41/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X65 : $i, X67 : $i, X68 : $i]:
% 0.41/0.59         ((r1_tarski @ X67 @ (k2_tarski @ X65 @ X68))
% 0.41/0.59          | ((X67) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X65 : $i, X68 : $i]:
% 0.41/0.59         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X65 @ X68))),
% 0.41/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.41/0.59  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['18', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.41/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.41/0.59           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['23', '26'])).
% 0.41/0.59  thf(t5_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.59  thf('28', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf(t48_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.41/0.59           = (k3_xboole_0 @ X17 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.41/0.59           = (k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.59  thf('32', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.41/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['31', '34', '35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.41/0.59         = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['17', '37'])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.59        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '38'])).
% 0.41/0.59  thf(t20_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.41/0.59         ( k1_tarski @ A ) ) <=>
% 0.41/0.59       ( ( A ) != ( B ) ) ))).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (![X69 : $i, X70 : $i]:
% 0.41/0.59         (((X70) != (X69))
% 0.41/0.59          | ((k4_xboole_0 @ (k1_tarski @ X70) @ (k1_tarski @ X69))
% 0.41/0.59              != (k1_tarski @ X70)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X69 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k1_tarski @ X69) @ (k1_tarski @ X69))
% 0.41/0.59           != (k1_tarski @ X69))),
% 0.41/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X69 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k1_tarski @ X69) @ (k1_tarski @ X69))
% 0.41/0.59           != (k1_tarski @ X69))),
% 0.41/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['31', '34', '35', '36'])).
% 0.41/0.59  thf('45', plain, (![X69 : $i]: ((k1_xboole_0) != (k1_tarski @ X69))),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('46', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.41/0.59      inference('clc', [status(thm)], ['39', '45'])).
% 0.41/0.59  thf(d2_tarski, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.41/0.59       ( ![D:$i]:
% 0.41/0.59         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X27 @ X25)
% 0.41/0.59          | ((X27) = (X26))
% 0.41/0.59          | ((X27) = (X23))
% 0.41/0.59          | ((X25) != (k2_tarski @ X26 @ X23)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_tarski])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X23 : $i, X26 : $i, X27 : $i]:
% 0.41/0.59         (((X27) = (X23))
% 0.41/0.59          | ((X27) = (X26))
% 0.41/0.59          | ~ (r2_hidden @ X27 @ (k2_tarski @ X26 @ X23)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.41/0.59  thf('49', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['46', '48'])).
% 0.41/0.59  thf('50', plain, (((sk_A) != (sk_D_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('51', plain, (((sk_A) != (sk_C_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('52', plain, ($false),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['49', '50', '51'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
