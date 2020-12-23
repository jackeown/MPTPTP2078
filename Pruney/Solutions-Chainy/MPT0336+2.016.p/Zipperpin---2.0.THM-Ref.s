%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rvSuohsSNG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:22 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 118 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  582 ( 879 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('29',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

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

thf('40',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ sk_A )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_C_2 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( ( k3_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
        = ( k3_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('61',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['2','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rvSuohsSNG
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.03/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.24  % Solved by: fo/fo7.sh
% 1.03/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.24  % done 1430 iterations in 0.773s
% 1.03/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.24  % SZS output start Refutation
% 1.03/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.03/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.03/1.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.03/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.24  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.03/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.03/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.03/1.24  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.03/1.24  thf(t149_zfmisc_1, conjecture,
% 1.03/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.24     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.03/1.24         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.03/1.24       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.03/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.24        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.03/1.24            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.03/1.24          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.03/1.24    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.03/1.24  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.03/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.24  thf(commutativity_k2_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.03/1.24  thf('1', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.03/1.24  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 1.03/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.03/1.24  thf(commutativity_k3_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.03/1.24  thf('3', plain,
% 1.03/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.24  thf(t17_xboole_1, axiom,
% 1.03/1.24    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.03/1.24  thf('4', plain,
% 1.03/1.24      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 1.03/1.24      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.03/1.24  thf('5', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.03/1.24      inference('sup+', [status(thm)], ['3', '4'])).
% 1.03/1.24  thf('6', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.03/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.24  thf(symmetry_r1_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.03/1.24  thf('7', plain,
% 1.03/1.24      (![X7 : $i, X8 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.03/1.24      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.03/1.24  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.03/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.03/1.24  thf(d7_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]:
% 1.03/1.24     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.03/1.24       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.03/1.24  thf('9', plain,
% 1.03/1.24      (![X4 : $i, X5 : $i]:
% 1.03/1.24         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.03/1.24      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.03/1.24  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.03/1.24      inference('sup-', [status(thm)], ['8', '9'])).
% 1.03/1.24  thf(t77_xboole_1, axiom,
% 1.03/1.24    (![A:$i,B:$i,C:$i]:
% 1.03/1.24     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.03/1.24          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.03/1.24  thf('11', plain,
% 1.03/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X24 @ X25)
% 1.03/1.24          | ~ (r1_xboole_0 @ X24 @ (k3_xboole_0 @ X25 @ X26))
% 1.03/1.24          | ~ (r1_tarski @ X24 @ X26))),
% 1.03/1.24      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.03/1.24  thf('12', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.03/1.24          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.03/1.24          | (r1_xboole_0 @ X0 @ sk_B))),
% 1.03/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.24  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.03/1.24  thf('13', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 1.03/1.24      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.03/1.24  thf('14', plain,
% 1.03/1.24      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.03/1.24      inference('demod', [status(thm)], ['12', '13'])).
% 1.03/1.24  thf('15', plain,
% 1.03/1.24      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2) @ sk_B)),
% 1.03/1.24      inference('sup-', [status(thm)], ['5', '14'])).
% 1.03/1.24  thf('16', plain,
% 1.03/1.24      (![X7 : $i, X8 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.03/1.24      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.03/1.24  thf('17', plain,
% 1.03/1.24      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C_2))),
% 1.03/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.03/1.24  thf('18', plain,
% 1.03/1.24      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 1.03/1.24      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.03/1.24  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.03/1.24      inference('sup-', [status(thm)], ['8', '9'])).
% 1.03/1.24  thf('20', plain,
% 1.03/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.24  thf('21', plain,
% 1.03/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X24 @ X25)
% 1.03/1.24          | ~ (r1_xboole_0 @ X24 @ (k3_xboole_0 @ X25 @ X26))
% 1.03/1.24          | ~ (r1_tarski @ X24 @ X26))),
% 1.03/1.24      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.03/1.24  thf('22', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.24         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.24          | ~ (r1_tarski @ X2 @ X1)
% 1.03/1.24          | (r1_xboole_0 @ X2 @ X0))),
% 1.03/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.03/1.24  thf('23', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.03/1.24          | (r1_xboole_0 @ X0 @ sk_C_2)
% 1.03/1.24          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.03/1.24      inference('sup-', [status(thm)], ['19', '22'])).
% 1.03/1.24  thf('24', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 1.03/1.24      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.03/1.24  thf('25', plain,
% 1.03/1.24      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_2) | ~ (r1_tarski @ X0 @ sk_B))),
% 1.03/1.24      inference('demod', [status(thm)], ['23', '24'])).
% 1.03/1.24  thf('26', plain,
% 1.03/1.24      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_2)),
% 1.03/1.24      inference('sup-', [status(thm)], ['18', '25'])).
% 1.03/1.24  thf(t4_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]:
% 1.03/1.24     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.03/1.24            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.03/1.24       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.03/1.24            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.03/1.24  thf('27', plain,
% 1.03/1.24      (![X13 : $i, X14 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X13 @ X14)
% 1.03/1.24          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 1.03/1.24      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.03/1.24  thf(l27_zfmisc_1, axiom,
% 1.03/1.24    (![A:$i,B:$i]:
% 1.03/1.24     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.03/1.24  thf('28', plain,
% 1.03/1.24      (![X38 : $i, X39 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 1.03/1.24      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.03/1.24  thf('29', plain,
% 1.03/1.24      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.03/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.24  thf('30', plain,
% 1.03/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.24  thf('31', plain,
% 1.03/1.24      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.03/1.24      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.24  thf(t28_xboole_1, axiom,
% 1.03/1.24    (![A:$i,B:$i]:
% 1.03/1.24     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.03/1.24  thf('32', plain,
% 1.03/1.24      (![X21 : $i, X22 : $i]:
% 1.03/1.24         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 1.03/1.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.03/1.24  thf('33', plain,
% 1.03/1.24      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.03/1.24         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.03/1.24      inference('sup-', [status(thm)], ['31', '32'])).
% 1.03/1.24  thf('34', plain,
% 1.03/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.24  thf('35', plain,
% 1.03/1.24      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.03/1.24         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.03/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.03/1.24  thf('36', plain,
% 1.03/1.24      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.03/1.24         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 1.03/1.24          | ~ (r1_xboole_0 @ X13 @ X16))),
% 1.03/1.24      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.03/1.24  thf('37', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.03/1.24          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['35', '36'])).
% 1.03/1.24  thf('38', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.03/1.24          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['28', '37'])).
% 1.03/1.24  thf('39', plain,
% 1.03/1.24      (((r1_xboole_0 @ sk_B @ sk_A)
% 1.03/1.24        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['27', '38'])).
% 1.03/1.24  thf(t3_xboole_0, axiom,
% 1.03/1.24    (![A:$i,B:$i]:
% 1.03/1.24     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.03/1.24            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.03/1.24       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.03/1.24            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.03/1.24  thf('40', plain,
% 1.03/1.24      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.03/1.24         (~ (r2_hidden @ X11 @ X9)
% 1.03/1.24          | ~ (r2_hidden @ X11 @ X12)
% 1.03/1.24          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.03/1.24      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.03/1.24  thf('41', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ sk_B @ sk_A)
% 1.03/1.24          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.03/1.24          | ~ (r2_hidden @ sk_D @ X0))),
% 1.03/1.24      inference('sup-', [status(thm)], ['39', '40'])).
% 1.03/1.24  thf('42', plain,
% 1.03/1.24      ((~ (r2_hidden @ sk_D @ sk_C_2) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.03/1.24      inference('sup-', [status(thm)], ['26', '41'])).
% 1.03/1.24  thf('43', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.03/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.24  thf('44', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.03/1.24      inference('demod', [status(thm)], ['42', '43'])).
% 1.03/1.24  thf(t78_xboole_1, axiom,
% 1.03/1.24    (![A:$i,B:$i,C:$i]:
% 1.03/1.24     ( ( r1_xboole_0 @ A @ B ) =>
% 1.03/1.24       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.03/1.24         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.03/1.24  thf('45', plain,
% 1.03/1.24      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.03/1.24         (~ (r1_xboole_0 @ X27 @ X28)
% 1.03/1.24          | ((k3_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 1.03/1.24              = (k3_xboole_0 @ X27 @ X29)))),
% 1.03/1.24      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.03/1.24  thf('46', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.03/1.24           = (k3_xboole_0 @ sk_B @ X0))),
% 1.03/1.24      inference('sup-', [status(thm)], ['44', '45'])).
% 1.03/1.24  thf('47', plain,
% 1.03/1.24      (![X13 : $i, X14 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X13 @ X14)
% 1.03/1.24          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 1.03/1.24      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.03/1.24  thf('48', plain,
% 1.03/1.24      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 1.03/1.24      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.03/1.24  thf('49', plain,
% 1.03/1.24      (![X21 : $i, X22 : $i]:
% 1.03/1.24         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 1.03/1.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.03/1.24  thf('50', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]:
% 1.03/1.24         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.03/1.24           = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.24      inference('sup-', [status(thm)], ['48', '49'])).
% 1.03/1.24  thf('51', plain,
% 1.03/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.24  thf('52', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]:
% 1.03/1.24         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.03/1.24           = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.24      inference('demod', [status(thm)], ['50', '51'])).
% 1.03/1.24  thf('53', plain,
% 1.03/1.24      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.03/1.24         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 1.03/1.24          | ~ (r1_xboole_0 @ X13 @ X16))),
% 1.03/1.24      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.03/1.24  thf('54', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.24         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.24          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['52', '53'])).
% 1.03/1.24  thf('55', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X1 @ X0)
% 1.03/1.24          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['47', '54'])).
% 1.03/1.24  thf('56', plain,
% 1.03/1.24      (![X0 : $i]:
% 1.03/1.24         (~ (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0))
% 1.03/1.24          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.03/1.24      inference('sup-', [status(thm)], ['46', '55'])).
% 1.03/1.24  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.03/1.24      inference('sup-', [status(thm)], ['17', '56'])).
% 1.03/1.24  thf('58', plain,
% 1.03/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.03/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.03/1.24  thf('59', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 1.03/1.24      inference('demod', [status(thm)], ['57', '58'])).
% 1.03/1.24  thf('60', plain,
% 1.03/1.24      (![X7 : $i, X8 : $i]:
% 1.03/1.24         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.03/1.24      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.03/1.24  thf('61', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 1.03/1.24      inference('sup-', [status(thm)], ['59', '60'])).
% 1.03/1.24  thf('62', plain, ($false), inference('demod', [status(thm)], ['2', '61'])).
% 1.03/1.24  
% 1.03/1.24  % SZS output end Refutation
% 1.03/1.24  
% 1.08/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
