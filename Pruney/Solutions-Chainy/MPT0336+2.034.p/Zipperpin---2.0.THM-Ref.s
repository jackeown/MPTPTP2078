%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UXTVWtncEM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 114 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  611 (1080 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_4 ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_4 @ X0 )
      | ( r1_xboole_0 @ sk_C_4 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C_4 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r2_hidden @ sk_D_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_4 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C_2 @ X19 @ X18 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C_2 @ X19 @ X18 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['3','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UXTVWtncEM
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.45/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.45/1.64  % Solved by: fo/fo7.sh
% 1.45/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.64  % done 1957 iterations in 1.187s
% 1.45/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.45/1.64  % SZS output start Refutation
% 1.45/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.45/1.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.45/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.45/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.45/1.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.45/1.64  thf(sk_C_4_type, type, sk_C_4: $i).
% 1.45/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.45/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.45/1.64  thf(t149_zfmisc_1, conjecture,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.45/1.64         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.45/1.64       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.45/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.45/1.64            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.45/1.64          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.45/1.64    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.45/1.64  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('1', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(symmetry_r1_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.45/1.64  thf('2', plain,
% 1.45/1.64      (![X12 : $i, X13 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X12 @ X13) | ~ (r1_xboole_0 @ X13 @ X12))),
% 1.45/1.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.45/1.64  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_4)),
% 1.45/1.64      inference('sup-', [status(thm)], ['1', '2'])).
% 1.45/1.64  thf(t3_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.45/1.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.45/1.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.45/1.64            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.45/1.64  thf('4', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('5', plain,
% 1.45/1.64      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(commutativity_k3_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.45/1.64  thf('6', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf('7', plain,
% 1.45/1.64      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.45/1.64      inference('demod', [status(thm)], ['5', '6'])).
% 1.45/1.64  thf(d3_tarski, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( r1_tarski @ A @ B ) <=>
% 1.45/1.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.45/1.64  thf('8', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X2 @ X3)
% 1.45/1.64          | (r2_hidden @ X2 @ X4)
% 1.45/1.64          | ~ (r1_tarski @ X3 @ X4))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_tarski])).
% 1.45/1.64  thf('9', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((r2_hidden @ X0 @ (k1_tarski @ sk_D_1))
% 1.45/1.64          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['7', '8'])).
% 1.45/1.64  thf('10', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.45/1.64          | (r2_hidden @ (sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0) @ 
% 1.45/1.64             (k1_tarski @ sk_D_1)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['4', '9'])).
% 1.45/1.64  thf('11', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('12', plain,
% 1.45/1.64      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X16 @ X14)
% 1.45/1.64          | ~ (r2_hidden @ X16 @ X17)
% 1.45/1.64          | ~ (r1_xboole_0 @ X14 @ X17))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('13', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X1 @ X0)
% 1.45/1.64          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.45/1.64          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['11', '12'])).
% 1.45/1.64  thf('14', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.45/1.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 1.45/1.64          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf('15', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf(d1_tarski, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.45/1.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.45/1.64  thf('16', plain,
% 1.45/1.64      (![X26 : $i, X28 : $i, X29 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X29 @ X28)
% 1.45/1.64          | ((X29) = (X26))
% 1.45/1.64          | ((X28) != (k1_tarski @ X26)))),
% 1.45/1.64      inference('cnf', [status(esa)], [d1_tarski])).
% 1.45/1.64  thf('17', plain,
% 1.45/1.64      (![X26 : $i, X29 : $i]:
% 1.45/1.64         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.45/1.64  thf('18', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.45/1.64          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '17'])).
% 1.45/1.64  thf('19', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('20', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((r2_hidden @ X0 @ X1)
% 1.45/1.64          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.45/1.64          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.45/1.64      inference('sup+', [status(thm)], ['18', '19'])).
% 1.45/1.64  thf('21', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.45/1.64      inference('simplify', [status(thm)], ['20'])).
% 1.45/1.64  thf(t70_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.45/1.64            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.45/1.64       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.45/1.64            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.45/1.64  thf('22', plain,
% 1.45/1.64      (![X22 : $i, X23 : $i, X25 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X22 @ X23)
% 1.45/1.64          | ~ (r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X25)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.45/1.64  thf('23', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.45/1.64          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['21', '22'])).
% 1.45/1.64  thf('24', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('25', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('26', plain,
% 1.45/1.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 1.45/1.64          | ~ (r1_xboole_0 @ X22 @ X23)
% 1.45/1.64          | ~ (r1_xboole_0 @ X22 @ X24))),
% 1.45/1.64      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.45/1.64  thf('27', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (~ (r1_xboole_0 @ sk_C_4 @ X0)
% 1.45/1.64          | (r1_xboole_0 @ sk_C_4 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['25', '26'])).
% 1.45/1.64  thf('28', plain, ((r1_xboole_0 @ sk_C_4 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.45/1.64      inference('sup-', [status(thm)], ['24', '27'])).
% 1.45/1.64  thf('29', plain, ((r2_hidden @ sk_D_1 @ sk_C_4)),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('30', plain,
% 1.45/1.64      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X16 @ X14)
% 1.45/1.64          | ~ (r2_hidden @ X16 @ X17)
% 1.45/1.64          | ~ (r1_xboole_0 @ X14 @ X17))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('31', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (~ (r1_xboole_0 @ sk_C_4 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['29', '30'])).
% 1.45/1.64  thf('32', plain, (~ (r2_hidden @ sk_D_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.45/1.64      inference('sup-', [status(thm)], ['28', '31'])).
% 1.45/1.64  thf('33', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B)),
% 1.45/1.64      inference('sup-', [status(thm)], ['23', '32'])).
% 1.45/1.64  thf('34', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('35', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.64  thf(d4_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.45/1.64       ( ![D:$i]:
% 1.45/1.64         ( ( r2_hidden @ D @ C ) <=>
% 1.45/1.64           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.45/1.64  thf('36', plain,
% 1.45/1.64      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X10 @ X9)
% 1.45/1.64          | (r2_hidden @ X10 @ X8)
% 1.45/1.64          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.45/1.64  thf('37', plain,
% 1.45/1.64      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.45/1.64         ((r2_hidden @ X10 @ X8)
% 1.45/1.64          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['36'])).
% 1.45/1.64  thf('38', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['35', '37'])).
% 1.45/1.64  thf('39', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.45/1.64          | (r2_hidden @ (sk_C_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['34', '38'])).
% 1.45/1.64  thf('40', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X1 @ X0)
% 1.45/1.64          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.45/1.64          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['11', '12'])).
% 1.45/1.64  thf('41', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 1.45/1.64          | ~ (r1_xboole_0 @ X2 @ X0)
% 1.45/1.64          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['39', '40'])).
% 1.45/1.64  thf('42', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         (~ (r1_xboole_0 @ X2 @ X0)
% 1.45/1.64          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 1.45/1.64      inference('simplify', [status(thm)], ['41'])).
% 1.45/1.64  thf('43', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_D_1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['33', '42'])).
% 1.45/1.64  thf('44', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.45/1.64          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.45/1.64      inference('demod', [status(thm)], ['14', '43'])).
% 1.45/1.64  thf('45', plain,
% 1.45/1.64      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 1.45/1.64      inference('simplify', [status(thm)], ['44'])).
% 1.45/1.64  thf(t4_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.45/1.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.45/1.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.45/1.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.45/1.64  thf('46', plain,
% 1.45/1.64      (![X18 : $i, X19 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X18 @ X19)
% 1.45/1.64          | (r2_hidden @ (sk_C_2 @ X19 @ X18) @ (k3_xboole_0 @ X18 @ X19)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.45/1.64  thf('47', plain,
% 1.45/1.64      (![X18 : $i, X19 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X18 @ X19)
% 1.45/1.64          | (r2_hidden @ (sk_C_2 @ X19 @ X18) @ (k3_xboole_0 @ X18 @ X19)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.45/1.64  thf('48', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['35', '37'])).
% 1.45/1.64  thf('49', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['47', '48'])).
% 1.45/1.64  thf('50', plain,
% 1.45/1.64      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X16 @ X14)
% 1.45/1.64          | ~ (r2_hidden @ X16 @ X17)
% 1.45/1.64          | ~ (r1_xboole_0 @ X14 @ X17))),
% 1.45/1.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.45/1.64  thf('51', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X0 @ X1)
% 1.45/1.64          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.45/1.64          | ~ (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['49', '50'])).
% 1.45/1.64  thf('52', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X1 @ X0)
% 1.45/1.64          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.45/1.64          | (r1_xboole_0 @ X1 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['46', '51'])).
% 1.45/1.64  thf('53', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.45/1.64          | (r1_xboole_0 @ X1 @ X0))),
% 1.45/1.64      inference('simplify', [status(thm)], ['52'])).
% 1.45/1.64  thf('54', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.45/1.64      inference('sup-', [status(thm)], ['45', '53'])).
% 1.45/1.64  thf('55', plain,
% 1.45/1.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 1.45/1.64          | ~ (r1_xboole_0 @ X22 @ X23)
% 1.45/1.64          | ~ (r1_xboole_0 @ X22 @ X24))),
% 1.45/1.64      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.45/1.64  thf('56', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.45/1.64          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['54', '55'])).
% 1.45/1.64  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_4))),
% 1.45/1.64      inference('sup-', [status(thm)], ['3', '56'])).
% 1.45/1.64  thf('58', plain,
% 1.45/1.64      (![X12 : $i, X13 : $i]:
% 1.45/1.64         ((r1_xboole_0 @ X12 @ X13) | ~ (r1_xboole_0 @ X13 @ X12))),
% 1.45/1.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.45/1.64  thf('59', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 1.45/1.64      inference('sup-', [status(thm)], ['57', '58'])).
% 1.45/1.64  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 1.45/1.64  
% 1.45/1.64  % SZS output end Refutation
% 1.45/1.64  
% 1.45/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
