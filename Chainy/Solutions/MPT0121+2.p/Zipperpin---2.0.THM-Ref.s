%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0121+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZ18b3wYAx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 17.65s
% Output     : Refutation 17.65s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  350 ( 597 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ ( A @ D ) )
        & ( r1_xboole_0 @ ( B @ D ) )
        & ( r1_xboole_0 @ ( C @ D ) ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ ( A @ D ) )
          & ( r1_xboole_0 @ ( B @ D ) )
          & ( r1_xboole_0 @ ( C @ D ) ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) @ sk_D_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) @ sk_D_4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ ( sk_C_5 @ sk_D_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ ( sk_D_4 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_D_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ ( sk_D_4 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('9',plain,(
    ! [X320: $i,X321: $i,X322: $i] :
      ( ( r1_xboole_0 @ ( X320 @ ( k2_xboole_0 @ ( X321 @ X322 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X320 @ X321 ) )
      | ~ ( r1_xboole_0 @ ( X320 @ X322 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_D_4 @ X0 ) )
      | ( r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_D_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    r1_xboole_0 @ ( sk_D_4 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X320: $i,X321: $i,X322: $i] :
      ( ( r1_xboole_0 @ ( X320 @ ( k2_xboole_0 @ ( X321 @ X322 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X320 @ X321 ) )
      | ~ ( r1_xboole_0 @ ( X320 @ X322 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_D_4 @ X0 ) )
      | ( r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_D_4 @ X0 ) )
      | ( r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,(
    r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('24',plain,(
    ! [X179: $i,X180: $i] :
      ( ( k3_xboole_0 @ ( X179 @ ( k2_xboole_0 @ ( X179 @ X180 ) ) ) )
      = X179 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('27',plain,(
    ! [X181: $i,X182: $i] :
      ( ( k2_xboole_0 @ ( X181 @ ( k3_xboole_0 @ ( X181 @ X182 ) ) ) )
      = X181 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X261: $i,X262: $i,X263: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X261 @ X262 ) @ X263 ) )
      = ( k2_xboole_0 @ ( X261 @ ( k2_xboole_0 @ ( X262 @ X263 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('34',plain,(
    r1_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','32','33'])).

thf('35',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['2','36'])).

%------------------------------------------------------------------------------
