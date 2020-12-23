%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5EuLv8FMd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:15 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  646 (1042 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k3_xboole_0 @ X34 @ X36 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('6',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_zfmisc_1 @ X28 @ X29 )
        = k1_xboole_0 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k2_zfmisc_1 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('17',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_zfmisc_1 @ X28 @ X29 )
        = k1_xboole_0 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('24',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ ( k2_xboole_0 @ X30 @ X32 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X30 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_B @ X1 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ ( k2_xboole_0 @ X30 @ X32 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X30 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D_1 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['12','43'])).

thf('45',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X30 @ X32 ) @ X31 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ X1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X30 @ X32 ) @ X31 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5EuLv8FMd
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.50  % Solved by: fo/fo7.sh
% 1.30/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.50  % done 1618 iterations in 1.071s
% 1.30/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.50  % SZS output start Refutation
% 1.30/1.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.30/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.30/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.30/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.30/1.50  thf(t127_zfmisc_1, conjecture,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.50     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 1.30/1.50       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.30/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.50        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 1.30/1.50          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 1.30/1.50    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 1.30/1.50  thf('0', plain,
% 1.30/1.50      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 1.30/1.50          (k2_zfmisc_1 @ sk_B @ sk_D_1))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('1', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('2', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_C_1 @ sk_D_1)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.30/1.50      inference('split', [status(esa)], ['1'])).
% 1.30/1.50  thf(d7_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.30/1.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.30/1.50  thf('3', plain,
% 1.30/1.50      (![X10 : $i, X11 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 1.30/1.50          | ~ (r1_xboole_0 @ X10 @ X11))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('4', plain,
% 1.30/1.50      ((((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['2', '3'])).
% 1.30/1.50  thf(t122_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 1.30/1.50         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.30/1.50       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.30/1.50         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.30/1.50  thf('5', plain,
% 1.30/1.50      (![X34 : $i, X36 : $i, X37 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ X37 @ (k3_xboole_0 @ X34 @ X36))
% 1.30/1.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X37 @ X36)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 1.30/1.50  thf('6', plain,
% 1.30/1.50      (![X10 : $i, X12 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X10 @ X12)
% 1.30/1.50          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('7', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         (((k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.30/1.50          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.50  thf('8', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (((k2_zfmisc_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 1.30/1.50           | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C_1) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X0 @ sk_D_1))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['4', '7'])).
% 1.30/1.50  thf(t113_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.30/1.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.30/1.50  thf('9', plain,
% 1.30/1.50      (![X28 : $i, X29 : $i]:
% 1.30/1.50         (((k2_zfmisc_1 @ X28 @ X29) = (k1_xboole_0))
% 1.30/1.50          | ((X29) != (k1_xboole_0)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.30/1.50  thf('10', plain,
% 1.30/1.50      (![X28 : $i]: ((k2_zfmisc_1 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 1.30/1.50      inference('simplify', [status(thm)], ['9'])).
% 1.30/1.50  thf('11', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.50           | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C_1) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X0 @ sk_D_1))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.30/1.50      inference('demod', [status(thm)], ['8', '10'])).
% 1.30/1.50  thf('12', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C_1) @ 
% 1.30/1.50           (k2_zfmisc_1 @ X0 @ sk_D_1)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['11'])).
% 1.30/1.50  thf('13', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('split', [status(esa)], ['1'])).
% 1.30/1.50  thf('14', plain,
% 1.30/1.50      (![X10 : $i, X11 : $i]:
% 1.30/1.50         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 1.30/1.50          | ~ (r1_xboole_0 @ X10 @ X11))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('15', plain,
% 1.30/1.50      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['13', '14'])).
% 1.30/1.50  thf('16', plain,
% 1.30/1.50      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X34 @ X36) @ X35)
% 1.30/1.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X36 @ X35)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 1.30/1.50  thf('17', plain,
% 1.30/1.50      (![X10 : $i, X12 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X10 @ X12)
% 1.30/1.50          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.30/1.50  thf('18', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         (((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 1.30/1.50          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['16', '17'])).
% 1.30/1.50  thf('19', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.30/1.50           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.30/1.50              (k2_zfmisc_1 @ sk_B @ X0))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['15', '18'])).
% 1.30/1.50  thf('20', plain,
% 1.30/1.50      (![X28 : $i, X29 : $i]:
% 1.30/1.50         (((k2_zfmisc_1 @ X28 @ X29) = (k1_xboole_0))
% 1.30/1.50          | ((X28) != (k1_xboole_0)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.30/1.50  thf('21', plain,
% 1.30/1.50      (![X29 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 1.30/1.50      inference('simplify', [status(thm)], ['20'])).
% 1.30/1.50  thf('22', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.50           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.30/1.50              (k2_zfmisc_1 @ sk_B @ X0))))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('demod', [status(thm)], ['19', '21'])).
% 1.30/1.50  thf('23', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['22'])).
% 1.30/1.50  thf(t120_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.30/1.50         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.30/1.50       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.30/1.50         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.30/1.50  thf('24', plain,
% 1.30/1.50      (![X30 : $i, X32 : $i, X33 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ X33 @ (k2_xboole_0 @ X30 @ X32))
% 1.30/1.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X33 @ X30) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X33 @ X32)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.30/1.50  thf(t70_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.30/1.50            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.30/1.50       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.30/1.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.30/1.50  thf('25', plain,
% 1.30/1.50      (![X20 : $i, X21 : $i, X23 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X20 @ X21)
% 1.30/1.50          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.30/1.50  thf('26', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.30/1.50          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['24', '25'])).
% 1.30/1.50  thf('27', plain,
% 1.30/1.50      ((![X0 : $i, X1 : $i]:
% 1.30/1.50          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.30/1.50           (k2_zfmisc_1 @ sk_B @ X1)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['23', '26'])).
% 1.30/1.50  thf('28', plain,
% 1.30/1.50      (![X30 : $i, X32 : $i, X33 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ X33 @ (k2_xboole_0 @ X30 @ X32))
% 1.30/1.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X33 @ X30) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X33 @ X32)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.30/1.50  thf(d3_tarski, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.50  thf('29', plain,
% 1.30/1.50      (![X1 : $i, X3 : $i]:
% 1.30/1.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.50  thf(d3_xboole_0, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.30/1.50       ( ![D:$i]:
% 1.30/1.50         ( ( r2_hidden @ D @ C ) <=>
% 1.30/1.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.30/1.50  thf('30', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X4 @ X5)
% 1.30/1.50          | (r2_hidden @ X4 @ X6)
% 1.30/1.50          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.30/1.50  thf('31', plain,
% 1.30/1.50      (![X4 : $i, X5 : $i, X7 : $i]:
% 1.30/1.50         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 1.30/1.50      inference('simplify', [status(thm)], ['30'])).
% 1.30/1.50  thf('32', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((r1_tarski @ X0 @ X1)
% 1.30/1.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['29', '31'])).
% 1.30/1.50  thf('33', plain,
% 1.30/1.50      (![X1 : $i, X3 : $i]:
% 1.30/1.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.50  thf('34', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.30/1.50          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['32', '33'])).
% 1.30/1.50  thf('35', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.30/1.50      inference('simplify', [status(thm)], ['34'])).
% 1.30/1.50  thf(t63_xboole_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.30/1.50       ( r1_xboole_0 @ A @ C ) ))).
% 1.30/1.50  thf('36', plain,
% 1.30/1.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.30/1.50         (~ (r1_tarski @ X17 @ X18)
% 1.30/1.50          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.30/1.50          | (r1_xboole_0 @ X17 @ X19))),
% 1.30/1.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.30/1.50  thf('37', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X0 @ X2)
% 1.30/1.50          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.30/1.50      inference('sup-', [status(thm)], ['35', '36'])).
% 1.30/1.50  thf('38', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 1.30/1.50          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ X3))),
% 1.30/1.50      inference('sup-', [status(thm)], ['28', '37'])).
% 1.30/1.50  thf('39', plain,
% 1.30/1.50      ((![X0 : $i, X1 : $i]:
% 1.30/1.50          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 1.30/1.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['27', '38'])).
% 1.30/1.50  thf('40', plain,
% 1.30/1.50      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 1.30/1.50          (k2_zfmisc_1 @ sk_B @ sk_D_1))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('41', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 1.30/1.50      inference('sup-', [status(thm)], ['39', '40'])).
% 1.30/1.50  thf('42', plain,
% 1.30/1.50      (((r1_xboole_0 @ sk_C_1 @ sk_D_1)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 1.30/1.50      inference('split', [status(esa)], ['1'])).
% 1.30/1.50  thf('43', plain, (((r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 1.30/1.50  thf('44', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C_1) @ 
% 1.30/1.50          (k2_zfmisc_1 @ X0 @ sk_D_1))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['12', '43'])).
% 1.30/1.50  thf('45', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X30 @ X32) @ X31)
% 1.30/1.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X32 @ X31)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.30/1.50  thf('46', plain,
% 1.30/1.50      (![X20 : $i, X21 : $i, X23 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X20 @ X21)
% 1.30/1.50          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.30/1.50  thf('47', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 1.30/1.50          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['45', '46'])).
% 1.30/1.50  thf('48', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ sk_C_1) @ 
% 1.30/1.50          (k2_zfmisc_1 @ X1 @ sk_D_1))),
% 1.30/1.50      inference('sup-', [status(thm)], ['44', '47'])).
% 1.30/1.50  thf('49', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.30/1.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X30 @ X32) @ X31)
% 1.30/1.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 1.30/1.50              (k2_zfmisc_1 @ X32 @ X31)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.30/1.50  thf('50', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((r1_xboole_0 @ X0 @ X2)
% 1.30/1.50          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.30/1.50      inference('sup-', [status(thm)], ['35', '36'])).
% 1.30/1.50  thf('51', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 1.30/1.50          | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X3))),
% 1.30/1.50      inference('sup-', [status(thm)], ['49', '50'])).
% 1.30/1.50  thf('52', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 1.30/1.50          (k2_zfmisc_1 @ X0 @ sk_D_1))),
% 1.30/1.50      inference('sup-', [status(thm)], ['48', '51'])).
% 1.30/1.50  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 1.30/1.50  
% 1.30/1.50  % SZS output end Refutation
% 1.30/1.50  
% 1.30/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
