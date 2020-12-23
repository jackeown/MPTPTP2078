%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWDugPrR0M

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 232 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  733 (2231 expanded)
%              Number of equality atoms :   73 ( 173 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_D_1 @ X42 @ X40 ) ) @ X40 )
      | ( X41
       != ( k1_relat_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_D_1 @ X42 @ X40 ) ) @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X47 @ X45 ) @ X46 )
      | ( r2_hidden @ X45 @ ( k11_relat_1 @ X46 @ X47 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X31 @ X32 ) )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ X0 ) )
        = ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ X0 ) )
        = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ X0 ) )
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ X0 ) )
        = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 != X33 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) )
     != ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
     != ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('43',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k11_relat_1 @ X46 @ X47 ) )
      | ( r2_hidden @ ( k4_tarski @ X47 @ X45 ) @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X38 @ X39 ) @ X40 )
      | ( r2_hidden @ X38 @ X41 )
      | ( X41
       != ( k1_relat_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X38 @ ( k1_relat_1 @ X40 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X38 @ X39 ) @ X40 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GWDugPrR0M
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 213 iterations in 0.076s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t205_relat_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ B ) =>
% 0.20/0.53          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.53            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('2', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.20/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf(d4_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X42 @ X41)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X42 @ (sk_D_1 @ X42 @ X40)) @ X40)
% 0.20/0.53          | ((X41) != (k1_relat_1 @ X40)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X40 : $i, X42 : $i]:
% 0.20/0.53         ((r2_hidden @ (k4_tarski @ X42 @ (sk_D_1 @ X42 @ X40)) @ X40)
% 0.20/0.53          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ X40)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.53  thf(t204_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.53         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X47 @ X45) @ X46)
% 0.20/0.53          | (r2_hidden @ X45 @ (k11_relat_1 @ X46 @ X47))
% 0.20/0.53          | ~ (v1_relat_1 @ X46))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.53            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['3', '12'])).
% 0.20/0.53  thf(l1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X26 : $i, X28 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((r1_tarski @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ k1_xboole_0))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t3_xboole_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t19_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.53       ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X31 @ X32))
% 0.20/0.53           = (k1_tarski @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((k3_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53            (k2_tarski @ (sk_D_1 @ sk_A @ sk_B_1) @ X0))
% 0.20/0.53            = (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((k3_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53            (k2_tarski @ (sk_D_1 @ sk_A @ sk_B_1) @ X0)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((k4_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53            (k2_tarski @ (sk_D_1 @ sk_A @ sk_B_1) @ X0))
% 0.20/0.53            = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf(t21_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf(t46_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.53  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((k4_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53            (k2_tarski @ (sk_D_1 @ sk_A @ sk_B_1) @ X0)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)))
% 0.20/0.53          = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t20_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X33 : $i, X34 : $i]:
% 0.20/0.53         (((X34) != (X33))
% 0.20/0.53          | ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X33))
% 0.20/0.53              != (k1_tarski @ X34)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X33 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))
% 0.20/0.53           != (k1_tarski @ X33))),
% 0.20/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ k1_xboole_0)
% 0.20/0.53          != (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['32', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X45 @ (k11_relat_1 @ X46 @ X47))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X47 @ X45) @ X46)
% 0.20/0.53          | ~ (v1_relat_1 @ X46))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.20/0.53             X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X38 @ X39) @ X40)
% 0.20/0.53          | (r2_hidden @ X38 @ X41)
% 0.20/0.53          | ((X41) != (k1_relat_1 @ X40)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.53         ((r2_hidden @ X38 @ (k1_relat_1 @ X40))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X38 @ X39) @ X40))),
% 0.20/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.53         | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.53             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.53  thf('55', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '54'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
