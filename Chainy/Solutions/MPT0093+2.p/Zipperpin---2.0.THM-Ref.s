%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0093+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FDALgyYHw4

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 42.62s
% Output     : Refutation 42.62s
% Verified   : 
% Statistics : Number of formulae       :   65 (  73 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 ( 480 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) )
     => ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) )
       => ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('4',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
    = sk_C_5 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( k4_xboole_0 @ ( X88 @ ( k3_xboole_0 @ ( X89 @ X90 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X88 @ X89 ) @ ( k4_xboole_0 @ ( X88 @ X90 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( sk_C_5 @ ( k4_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('8',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) )
      = sk_C_5 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('14',plain,(
    ! [X297: $i,X298: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X297 @ X298 ) @ X298 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_C_5 ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('20',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( X0 @ sk_C_5 ) ) ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X114: $i,X115: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X114 @ X115 ) @ X114 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('25',plain,(
    ! [X149: $i,X150: $i] :
      ( ( ( k3_xboole_0 @ ( X149 @ X150 ) )
        = X149 )
      | ~ ( r1_tarski @ ( X149 @ X150 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('29',plain,(
    ! [X116: $i,X117: $i,X118: $i] :
      ( ( r1_tarski @ ( X116 @ X117 ) )
      | ~ ( r1_tarski @ ( X116 @ ( k3_xboole_0 @ ( X117 @ X118 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( r1_tarski @ ( X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k4_xboole_0 @ ( A @ C ) @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X164: $i,X165: $i,X166: $i] :
      ( ~ ( r1_tarski @ ( X164 @ X165 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( X164 @ X166 ) @ ( k4_xboole_0 @ ( X165 @ X166 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) @ X1 ) @ ( k4_xboole_0 @ ( sk_B_2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( sk_A_2 @ X1 ) ) ) @ ( k4_xboole_0 @ ( sk_B_2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ sk_A_2 ) @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('38',plain,(
    ! [X44: $i] :
      ( ( k3_xboole_0 @ ( X44 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('39',plain,(
    r1_tarski @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
