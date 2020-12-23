%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.biczF1xhGq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 141 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  795 (1344 expanded)
%              Number of equality atoms :   48 (  85 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ( ( ( k10_relat_1 @ X46 @ ( k2_relat_1 @ X46 ) )
        = ( k1_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k10_relat_1 @ X45 @ X43 ) )
      | ( r2_hidden @ ( k4_tarski @ X44 @ ( sk_D @ X45 @ X43 @ X44 ) ) @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X49 @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ ( k11_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ ( k4_tarski @ X44 @ X42 ) @ X45 )
      | ~ ( r2_hidden @ X42 @ ( k2_relat_1 @ X45 ) )
      | ( r2_hidden @ X44 @ ( k10_relat_1 @ X45 @ X43 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B_1 )
        | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,(
    ! [X46: $i] :
      ( ( ( k10_relat_1 @ X46 @ ( k2_relat_1 @ X46 ) )
        = ( k1_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k10_relat_1 @ X45 @ X43 ) )
      | ( r2_hidden @ ( sk_D @ X45 @ X43 @ X44 ) @ X43 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k10_relat_1 @ X45 @ X43 ) )
      | ( r2_hidden @ ( sk_D @ X45 @ X43 @ X44 ) @ X43 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('38',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('40',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['40','43','44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k11_relat_1 @ X48 @ X49 ) )
      | ( r2_hidden @ ( k4_tarski @ X49 @ X47 ) @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('52',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X50 @ X51 ) @ X52 )
      | ( r2_hidden @ X50 @ ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.biczF1xhGq
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:55 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 215 iterations in 0.150s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.62  thf(t205_relat_1, conjecture,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ B ) =>
% 0.36/0.62       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.36/0.62         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i,B:$i]:
% 0.36/0.62        ( ( v1_relat_1 @ B ) =>
% 0.36/0.62          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.36/0.62            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.36/0.62        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.62       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.36/0.62         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.36/0.62        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf(t169_relat_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ A ) =>
% 0.36/0.62       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      (![X46 : $i]:
% 0.36/0.62         (((k10_relat_1 @ X46 @ (k2_relat_1 @ X46)) = (k1_relat_1 @ X46))
% 0.36/0.62          | ~ (v1_relat_1 @ X46))),
% 0.36/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.62  thf(t166_relat_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ C ) =>
% 0.36/0.62       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.36/0.62         ( ?[D:$i]:
% 0.36/0.62           ( ( r2_hidden @ D @ B ) & 
% 0.36/0.62             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.36/0.62             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X44 @ (k10_relat_1 @ X45 @ X43))
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ X44 @ (sk_D @ X45 @ X43 @ X44)) @ X45)
% 0.36/0.62          | ~ (v1_relat_1 @ X45))),
% 0.36/0.62      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | (r2_hidden @ 
% 0.36/0.62             (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((r2_hidden @ 
% 0.36/0.62           (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62         | (r2_hidden @ 
% 0.36/0.62            (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.36/0.62            sk_B_1)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['4', '8'])).
% 0.36/0.62  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (((r2_hidden @ 
% 0.36/0.62         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.36/0.62         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf(t204_relat_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ C ) =>
% 0.36/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.36/0.62         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.36/0.62         (~ (r2_hidden @ (k4_tarski @ X49 @ X47) @ X48)
% 0.36/0.62          | (r2_hidden @ X47 @ (k11_relat_1 @ X48 @ X49))
% 0.36/0.62          | ~ (v1_relat_1 @ X48))),
% 0.36/0.62      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.62  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62         (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62         k1_xboole_0))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['2', '15'])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (((r2_hidden @ 
% 0.36/0.62         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.36/0.62         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X42 @ X43)
% 0.36/0.62          | ~ (r2_hidden @ (k4_tarski @ X44 @ X42) @ X45)
% 0.36/0.62          | ~ (r2_hidden @ X42 @ (k2_relat_1 @ X45))
% 0.36/0.62          | (r2_hidden @ X44 @ (k10_relat_1 @ X45 @ X43))
% 0.36/0.62          | ~ (v1_relat_1 @ X45))),
% 0.36/0.62      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62           | (r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.36/0.62           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62                (k2_relat_1 @ sk_B_1))
% 0.36/0.62           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.62  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X46 : $i]:
% 0.36/0.62         (((k10_relat_1 @ X46 @ (k2_relat_1 @ X46)) = (k1_relat_1 @ X46))
% 0.36/0.62          | ~ (v1_relat_1 @ X46))),
% 0.36/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X44 @ (k10_relat_1 @ X45 @ X43))
% 0.36/0.62          | (r2_hidden @ (sk_D @ X45 @ X43 @ X44) @ X43)
% 0.36/0.62          | ~ (v1_relat_1 @ X45))),
% 0.36/0.62      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | (r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.36/0.62             (k2_relat_1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ (k2_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62            (k2_relat_1 @ sk_B_1))))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['21', '25'])).
% 0.36/0.62  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.36/0.62         (k2_relat_1 @ sk_B_1)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.36/0.62           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['19', '20', '28'])).
% 0.36/0.62  thf('30', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ k1_xboole_0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '29'])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X44 @ (k10_relat_1 @ X45 @ X43))
% 0.36/0.62          | (r2_hidden @ (sk_D @ X45 @ X43 @ X44) @ X43)
% 0.36/0.62          | ~ (v1_relat_1 @ X45))),
% 0.36/0.62      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62         | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.62  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('34', plain,
% 0.36/0.62      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.62  thf(l1_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (![X34 : $i, X36 : $i]:
% 0.36/0.62         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.36/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (((r1_tarski @ (k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) @ 
% 0.36/0.62         k1_xboole_0))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf(t3_xboole_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      ((((k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) = (k1_xboole_0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.62  thf(t20_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.62         ( k1_tarski @ A ) ) <=>
% 0.36/0.62       ( ( A ) != ( B ) ) ))).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X37 : $i, X38 : $i]:
% 0.36/0.62         (((X38) != (X37))
% 0.36/0.62          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.36/0.62              != (k1_tarski @ X38)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.36/0.62  thf('40', plain,
% 0.36/0.62      (![X37 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.36/0.62           != (k1_tarski @ X37))),
% 0.36/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.62  thf('41', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.62  thf(t100_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X2 @ X3)
% 0.36/0.62           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.62  thf(t92_xboole_1, axiom,
% 0.36/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('44', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.62  thf('45', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.36/0.62      inference('demod', [status(thm)], ['40', '43', '44'])).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.62         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.36/0.62             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['38', '45'])).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.62       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.62       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf(t7_xboole_0, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.62  thf('49', plain,
% 0.36/0.62      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.62  thf('50', plain,
% 0.36/0.62      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.36/0.62         (~ (r2_hidden @ X47 @ (k11_relat_1 @ X48 @ X49))
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ X49 @ X47) @ X48)
% 0.36/0.62          | ~ (v1_relat_1 @ X48))),
% 0.36/0.62      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.36/0.62          | ~ (v1_relat_1 @ X1)
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.36/0.62             X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.62  thf(t20_relat_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ C ) =>
% 0.36/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.36/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.62           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.36/0.62         (~ (r2_hidden @ (k4_tarski @ X50 @ X51) @ X52)
% 0.36/0.62          | (r2_hidden @ X50 @ (k1_relat_1 @ X52))
% 0.36/0.62          | ~ (v1_relat_1 @ X52))),
% 0.36/0.62      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ X0)
% 0.36/0.62          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.36/0.62  thf('55', plain,
% 0.36/0.62      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.36/0.62         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('56', plain,
% 0.36/0.62      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.62         | ((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.36/0.62         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('57', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('58', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.36/0.62         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.62  thf('59', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.36/0.62         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.62      inference('split', [status(esa)], ['3'])).
% 0.36/0.62  thf('60', plain,
% 0.36/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.62         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.36/0.62             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.62  thf('61', plain,
% 0.36/0.62      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.62       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.36/0.62  thf('62', plain, ($false),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '61'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
