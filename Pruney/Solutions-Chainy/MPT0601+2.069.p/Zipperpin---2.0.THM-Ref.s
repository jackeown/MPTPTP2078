%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Im1ie6mYgz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 149 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  834 (1383 expanded)
%              Number of equality atoms :   54 (  91 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

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
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k10_relat_1 @ X38 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ X37 @ ( sk_D @ X38 @ X36 @ X37 ) ) @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X40 ) @ X41 )
      | ( r2_hidden @ X40 @ ( k11_relat_1 @ X41 @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X37 @ X35 ) @ X38 )
      | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ X38 ) )
      | ( r2_hidden @ X37 @ ( k10_relat_1 @ X38 @ X36 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k10_relat_1 @ X38 @ X36 ) )
      | ( r2_hidden @ ( sk_D @ X38 @ X36 @ X37 ) @ X36 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k10_relat_1 @ X38 @ X36 ) )
      | ( r2_hidden @ ( sk_D @ X38 @ X36 @ X37 ) @ X36 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( X30 != X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X29 ) )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X29 ) )
     != ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('42',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,(
    ! [X29: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X29 ) ) ),
    inference(demod,[status(thm)],['40','47','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('54',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k11_relat_1 @ X41 @ X42 ) )
      | ( r2_hidden @ ( k4_tarski @ X42 @ X40 ) @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('56',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X43 @ X44 ) @ X45 )
      | ( r2_hidden @ X43 @ ( k1_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
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
    inference('sat_resolution*',[status(thm)],['1','51','52','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Im1ie6mYgz
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 234 iterations in 0.103s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.57  thf(t205_relat_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ B ) =>
% 0.22/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.57         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( v1_relat_1 @ B ) =>
% 0.22/0.57          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.57            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.57        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('split', [status(esa)], ['0'])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['0'])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.22/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('split', [status(esa)], ['3'])).
% 0.22/0.57  thf(t169_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X39 : $i]:
% 0.22/0.57         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.22/0.57          | ~ (v1_relat_1 @ X39))),
% 0.22/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.57  thf(t166_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ C ) =>
% 0.22/0.57       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.22/0.57         ( ?[D:$i]:
% 0.22/0.57           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.57             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.22/0.57             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X37 @ (k10_relat_1 @ X38 @ X36))
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X37 @ (sk_D @ X38 @ X36 @ X37)) @ X38)
% 0.22/0.57          | ~ (v1_relat_1 @ X38))),
% 0.22/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ 
% 0.22/0.57           (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57         | (r2_hidden @ 
% 0.22/0.57            (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.22/0.57            sk_B_1)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.57  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.22/0.57         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf(t204_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ C ) =>
% 0.22/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.57         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.57         (~ (r2_hidden @ (k4_tarski @ X42 @ X40) @ X41)
% 0.22/0.57          | (r2_hidden @ X40 @ (k11_relat_1 @ X41 @ X42))
% 0.22/0.57          | ~ (v1_relat_1 @ X41))),
% 0.22/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57         (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57         k1_xboole_0))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['2', '15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.22/0.57         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X35 @ X36)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X37 @ X35) @ X38)
% 0.22/0.57          | ~ (r2_hidden @ X35 @ (k2_relat_1 @ X38))
% 0.22/0.57          | (r2_hidden @ X37 @ (k10_relat_1 @ X38 @ X36))
% 0.22/0.57          | ~ (v1_relat_1 @ X38))),
% 0.22/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      ((![X0 : $i]:
% 0.22/0.57          (~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57           | (r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.22/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57                (k2_relat_1 @ sk_B_1))
% 0.22/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('split', [status(esa)], ['3'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X39 : $i]:
% 0.22/0.57         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.22/0.57          | ~ (v1_relat_1 @ X39))),
% 0.22/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X37 @ (k10_relat_1 @ X38 @ X36))
% 0.22/0.57          | (r2_hidden @ (sk_D @ X38 @ X36 @ X37) @ X36)
% 0.22/0.57          | ~ (v1_relat_1 @ X38))),
% 0.22/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.22/0.57             (k2_relat_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ (k2_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57            (k2_relat_1 @ sk_B_1))))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['21', '25'])).
% 0.22/0.57  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.22/0.57         (k2_relat_1 @ sk_B_1)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      ((![X0 : $i]:
% 0.22/0.57          ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.22/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['19', '20', '28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ k1_xboole_0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['16', '29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X37 @ (k10_relat_1 @ X38 @ X36))
% 0.22/0.57          | (r2_hidden @ (sk_D @ X38 @ X36 @ X37) @ X36)
% 0.22/0.57          | ~ (v1_relat_1 @ X38))),
% 0.22/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.57  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.57  thf(l1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X26 : $i, X28 : $i]:
% 0.22/0.57         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.22/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) @ 
% 0.22/0.57         k1_xboole_0))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf(t3_xboole_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      ((((k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) = (k1_xboole_0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf(t20_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.57         ( k1_tarski @ A ) ) <=>
% 0.22/0.57       ( ( A ) != ( B ) ) ))).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X29 : $i, X30 : $i]:
% 0.22/0.57         (((X30) != (X29))
% 0.22/0.57          | ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X29))
% 0.22/0.57              != (k1_tarski @ X30)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (![X29 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X29))
% 0.22/0.57           != (k1_tarski @ X29))),
% 0.22/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.57  thf(t69_enumset1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.57  thf('41', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.57  thf(t11_setfam_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.57  thf('42', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.22/0.57      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.22/0.57  thf(t12_setfam_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X33 : $i, X34 : $i]:
% 0.22/0.57         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.22/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.57  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf(t100_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.57  thf(t92_xboole_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('48', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.57  thf('49', plain, (![X29 : $i]: ((k1_xboole_0) != (k1_tarski @ X29))),
% 0.22/0.57      inference('demod', [status(thm)], ['40', '47', '48'])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.22/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['38', '49'])).
% 0.22/0.57  thf('51', plain,
% 0.22/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('split', [status(esa)], ['3'])).
% 0.22/0.57  thf(t7_xboole_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.57  thf('53', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X40 @ (k11_relat_1 @ X41 @ X42))
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X42 @ X40) @ X41)
% 0.22/0.57          | ~ (v1_relat_1 @ X41))),
% 0.22/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.22/0.57             X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.57  thf(t20_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ C ) =>
% 0.22/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.22/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.57           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.57         (~ (r2_hidden @ (k4_tarski @ X43 @ X44) @ X45)
% 0.22/0.57          | (r2_hidden @ X43 @ (k1_relat_1 @ X45))
% 0.22/0.57          | ~ (v1_relat_1 @ X45))),
% 0.22/0.57      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.57  thf('58', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.57          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.22/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('split', [status(esa)], ['0'])).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.57         | ((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.22/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.57  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('62', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['3'])).
% 0.22/0.57  thf('64', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.57             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.57  thf('65', plain,
% 0.22/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.57  thf('66', plain, ($false),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['1', '51', '52', '65'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
