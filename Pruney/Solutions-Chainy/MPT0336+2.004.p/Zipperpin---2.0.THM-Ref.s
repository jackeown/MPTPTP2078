%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x11Hl9l0W2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 108 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  704 ( 941 expanded)
%              Number of equality atoms :   84 (  98 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X41
        = ( k1_enumset1 @ X38 @ X39 @ X40 ) )
      | ( X41
        = ( k2_tarski @ X38 @ X40 ) )
      | ( X41
        = ( k2_tarski @ X39 @ X40 ) )
      | ( X41
        = ( k2_tarski @ X38 @ X39 ) )
      | ( X41
        = ( k1_tarski @ X40 ) )
      | ( X41
        = ( k1_tarski @ X39 ) )
      | ( X41
        = ( k1_tarski @ X38 ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X41 @ ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
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

thf('35',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('41',plain,(
    ! [X26: $i,X29: $i] :
      ( r2_hidden @ X26 @ ( k2_tarski @ X29 @ X26 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['46'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['2','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x11Hl9l0W2
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1617 iterations in 0.643s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.10  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(t149_zfmisc_1, conjecture,
% 0.90/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.90/1.10         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.90/1.10       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.90/1.10            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.90/1.10          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.90/1.10  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(commutativity_k2_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.90/1.10  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.90/1.10      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['3', '4'])).
% 0.90/1.10  thf(t69_enumset1, axiom,
% 0.90/1.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.10  thf('6', plain, (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.10  thf(t70_enumset1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X33 : $i, X34 : $i]:
% 0.90/1.10         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.10  thf(t142_zfmisc_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.10       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.90/1.10            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.90/1.10            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.90/1.10            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.90/1.10            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.90/1.10            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.90/1.10         (((X41) = (k1_enumset1 @ X38 @ X39 @ X40))
% 0.90/1.10          | ((X41) = (k2_tarski @ X38 @ X40))
% 0.90/1.10          | ((X41) = (k2_tarski @ X39 @ X40))
% 0.90/1.10          | ((X41) = (k2_tarski @ X38 @ X39))
% 0.90/1.10          | ((X41) = (k1_tarski @ X40))
% 0.90/1.10          | ((X41) = (k1_tarski @ X39))
% 0.90/1.10          | ((X41) = (k1_tarski @ X38))
% 0.90/1.10          | ((X41) = (k1_xboole_0))
% 0.90/1.10          | ~ (r1_tarski @ X41 @ (k1_enumset1 @ X38 @ X39 @ X40)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k1_xboole_0))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k1_tarski @ X0))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.10  thf('11', plain,
% 0.90/1.10      (![X33 : $i, X34 : $i]:
% 0.90/1.10         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k1_xboole_0))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k1_tarski @ X0))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (((X2) = (k2_tarski @ X1 @ X0))
% 0.90/1.10          | ((X2) = (k1_tarski @ X0))
% 0.90/1.10          | ((X2) = (k1_tarski @ X1))
% 0.90/1.10          | ((X2) = (k1_xboole_0))
% 0.90/1.10          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.90/1.10      inference('simplify', [status(thm)], ['12'])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_xboole_0))
% 0.90/1.10          | ((X1) = (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['6', '13'])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_xboole_0))
% 0.90/1.10          | ((X1) = (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_tarski @ X0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((X1) = (k1_tarski @ X0))
% 0.90/1.10          | ((X1) = (k1_xboole_0))
% 0.90/1.10          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.90/1.10      inference('simplify', [status(thm)], ['16'])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.90/1.10        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '17'])).
% 0.90/1.10  thf(t17_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.10  thf('19', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.90/1.10      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.10  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d7_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.90/1.10       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      (![X4 : $i, X5 : $i]:
% 0.90/1.10         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.90/1.10      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.10  thf('22', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.10  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.90/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.10  thf(t77_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.90/1.10          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X18 @ X19)
% 0.90/1.10          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.90/1.10          | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.10      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.10          | ~ (r1_tarski @ X2 @ X1)
% 0.90/1.10          | (r1_xboole_0 @ X2 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.10          | (r1_xboole_0 @ X0 @ sk_C_1)
% 0.90/1.10          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['24', '27'])).
% 0.90/1.10  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.90/1.10  thf('29', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_1) | ~ (r1_tarski @ X0 @ sk_B))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '29'])).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['19', '30'])).
% 0.90/1.10  thf(symmetry_r1_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.90/1.10      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.10  thf('34', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t3_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.90/1.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.10            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X11 @ X9)
% 0.90/1.10          | ~ (r2_hidden @ X11 @ X12)
% 0.90/1.10          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['33', '36'])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 0.90/1.10        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['18', '37'])).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.90/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.10  thf(d2_tarski, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.90/1.10       ( ![D:$i]:
% 0.90/1.10         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.10         (((X27) != (X26))
% 0.90/1.10          | (r2_hidden @ X27 @ X28)
% 0.90/1.10          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d2_tarski])).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (![X26 : $i, X29 : $i]: (r2_hidden @ X26 @ (k2_tarski @ X29 @ X26))),
% 0.90/1.10      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.10  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['39', '41'])).
% 0.90/1.10  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.90/1.10      inference('demod', [status(thm)], ['38', '42'])).
% 0.90/1.10  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.90/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (![X4 : $i, X6 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.10  thf('46', plain,
% 0.90/1.10      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.10  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.90/1.10      inference('simplify', [status(thm)], ['46'])).
% 0.90/1.10  thf(t78_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( r1_xboole_0 @ A @ B ) =>
% 0.90/1.10       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.90/1.10         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ X21 @ X22)
% 0.90/1.10          | ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.90/1.10              = (k3_xboole_0 @ X21 @ X23)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.90/1.10           = (k3_xboole_0 @ sk_B @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (![X4 : $i, X6 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['50', '51'])).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.90/1.10          | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['49', '52'])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.10        | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['43', '53'])).
% 0.90/1.10  thf('55', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.90/1.10      inference('simplify', [status(thm)], ['54'])).
% 0.90/1.10  thf('56', plain, ($false), inference('demod', [status(thm)], ['2', '55'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
