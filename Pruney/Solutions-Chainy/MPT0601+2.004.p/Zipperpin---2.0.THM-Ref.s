%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vm4fYIj4iU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  772 (1446 expanded)
%              Number of equality atoms :   53 ( 103 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_3 @ X23 @ X21 ) ) @ X21 )
      | ( X22
       != ( k1_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_3 @ X23 @ X21 ) ) @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_3 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_3 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k1_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_3 @ X23 @ X21 ) ) @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_3 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) ) @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) ) @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) @ X1 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ X0 @ k1_xboole_0 ) ) @ X1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('44',plain,
    ( ! [X1: $i] :
        ( ( k11_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('48',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ sk_A @ sk_B_1 ) ) @ X1 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_3 @ sk_A @ sk_B_1 ) ) @ X1 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('56',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vm4fYIj4iU
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 200 iterations in 0.180s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t205_relat_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.46/0.64         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( v1_relat_1 @ B ) =>
% 0.46/0.64          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.46/0.64            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.64       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf(d4_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X23 @ X22)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X23 @ (sk_D_3 @ X23 @ X21)) @ X21)
% 0.46/0.64          | ((X22) != (k1_relat_1 @ X21)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X21 : $i, X23 : $i]:
% 0.46/0.64         ((r2_hidden @ (k4_tarski @ X23 @ (sk_D_3 @ X23 @ X21)) @ X21)
% 0.46/0.64          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X21)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_3 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.64  thf(t204_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.64         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.46/0.64          | (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.46/0.64          | ~ (v1_relat_1 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (((~ (v1_relat_1 @ sk_B_1)
% 0.46/0.64         | (r2_hidden @ (sk_D_3 @ sk_A @ sk_B_1) @ 
% 0.46/0.64            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (((r2_hidden @ (sk_D_3 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((r2_hidden @ (sk_D_3 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.46/0.64             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['2', '11'])).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.46/0.64          | ~ (v1_relat_1 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.46/0.64             X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21)
% 0.46/0.64          | (r2_hidden @ X19 @ X22)
% 0.46/0.64          | ((X22) != (k1_relat_1 @ X21)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21))),
% 0.46/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X21 : $i, X23 : $i]:
% 0.46/0.64         ((r2_hidden @ (k4_tarski @ X23 @ (sk_D_3 @ X23 @ X21)) @ X21)
% 0.46/0.64          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X21)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X1 @ (sk_D_3 @ X1 @ X0)) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.46/0.64          | ~ (v1_relat_1 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.64           | ~ (v1_relat_1 @ sk_B_1)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.64           | ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | (r2_hidden @ 
% 0.46/0.64              (k4_tarski @ sk_A @ 
% 0.46/0.64               (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0))) @ 
% 0.46/0.64              sk_B_1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '25'])).
% 0.46/0.64  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t46_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.64  thf(fc2_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k4_xboole_0 @ X26 @ X27)))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X1 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | (r2_hidden @ 
% 0.46/0.64              (k4_tarski @ sk_A @ 
% 0.46/0.64               (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0))) @ 
% 0.46/0.64              sk_B_1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.46/0.64          | (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.46/0.64          | ~ (v1_relat_1 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | ~ (v1_relat_1 @ sk_B_1)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0)) @ 
% 0.46/0.64              (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain, ((v1_relat_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0)) @ 
% 0.46/0.64              k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.64  thf(d3_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64           ( ![C:$i,D:$i]:
% 0.46/0.64             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.46/0.64               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X15 @ X16)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ X16)
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0)) @ X1)
% 0.46/0.64           | ~ (r1_tarski @ k1_xboole_0 @ X1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '30'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('41', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ X0 @ k1_xboole_0)) @ X1)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.46/0.64  thf(t152_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      ((![X1 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.46/0.64          | ~ (v1_relat_1 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.46/0.64           | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ X1) @ k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '30'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ X1) @ k1_xboole_0)))
% 0.46/0.64         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ sk_A @ sk_B_1)) @ 
% 0.46/0.64           k1_xboole_0))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.46/0.64             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X15 @ X16)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ X16)
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.64           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ sk_A @ sk_B_1)) @ X1)
% 0.46/0.64           | ~ (r1_tarski @ k1_xboole_0 @ X1)))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.46/0.64             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '30'])).
% 0.46/0.64  thf('53', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      ((![X0 : $i, X1 : $i]:
% 0.46/0.64          (r2_hidden @ (k4_tarski @ X0 @ (sk_D_3 @ sk_A @ sk_B_1)) @ X1))
% 0.46/0.64         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.46/0.64             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.64       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.64       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.46/0.64         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.46/0.64         | ~ (v1_relat_1 @ sk_B_1)))
% 0.46/0.64         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.64  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.46/0.64         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.46/0.64         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.64         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.46/0.64             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.64       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.64  thf('66', plain, ($false),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '65'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.51/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
