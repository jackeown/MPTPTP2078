%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eH4nIBxR8Q

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 159 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  886 (1469 expanded)
%              Number of equality atoms :   59 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X47: $i] :
      ( ( ( k10_relat_1 @ X47 @ ( k2_relat_1 @ X47 ) )
        = ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k10_relat_1 @ X46 @ X44 ) )
      | ( r2_hidden @ ( k4_tarski @ X45 @ ( sk_D @ X46 @ X44 @ X45 ) ) @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X50 @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ ( k11_relat_1 @ X49 @ X50 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r2_hidden @ ( k4_tarski @ X45 @ X43 ) @ X46 )
      | ~ ( r2_hidden @ X43 @ ( k2_relat_1 @ X46 ) )
      | ( r2_hidden @ X45 @ ( k10_relat_1 @ X46 @ X44 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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
    ! [X47: $i] :
      ( ( ( k10_relat_1 @ X47 @ ( k2_relat_1 @ X47 ) )
        = ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k10_relat_1 @ X46 @ X44 ) )
      | ( r2_hidden @ ( sk_D @ X46 @ X44 @ X45 ) @ X44 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k10_relat_1 @ X46 @ X44 ) )
      | ( r2_hidden @ ( sk_D @ X46 @ X44 @ X45 ) @ X44 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('40',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
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

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','54'])).

thf('56',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('59',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X48 @ ( k11_relat_1 @ X49 @ X50 ) )
      | ( r2_hidden @ ( k4_tarski @ X50 @ X48 ) @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('61',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X51 @ X52 ) @ X53 )
      | ( r2_hidden @ X51 @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eH4nIBxR8Q
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.57  % Solved by: fo/fo7.sh
% 0.19/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.57  % done 329 iterations in 0.115s
% 0.19/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.57  % SZS output start Refutation
% 0.19/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.57  thf(t205_relat_1, conjecture,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ B ) =>
% 0.19/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.57         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.57    (~( ![A:$i,B:$i]:
% 0.19/0.57        ( ( v1_relat_1 @ B ) =>
% 0.19/0.57          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.57            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.57    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.57  thf('0', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.19/0.57        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('1', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('split', [status(esa)], ['0'])).
% 0.19/0.57  thf('2', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.19/0.57         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('split', [status(esa)], ['0'])).
% 0.19/0.57  thf('3', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.19/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('4', plain,
% 0.19/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('split', [status(esa)], ['3'])).
% 0.19/0.57  thf(t169_relat_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ A ) =>
% 0.19/0.57       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.19/0.57  thf('5', plain,
% 0.19/0.57      (![X47 : $i]:
% 0.19/0.57         (((k10_relat_1 @ X47 @ (k2_relat_1 @ X47)) = (k1_relat_1 @ X47))
% 0.19/0.57          | ~ (v1_relat_1 @ X47))),
% 0.19/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.57  thf(t166_relat_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ C ) =>
% 0.19/0.57       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.19/0.57         ( ?[D:$i]:
% 0.19/0.57           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.57             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.19/0.57             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.57  thf('6', plain,
% 0.19/0.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X45 @ (k10_relat_1 @ X46 @ X44))
% 0.19/0.57          | (r2_hidden @ (k4_tarski @ X45 @ (sk_D @ X46 @ X44 @ X45)) @ X46)
% 0.19/0.57          | ~ (v1_relat_1 @ X46))),
% 0.19/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.57  thf('7', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | (r2_hidden @ 
% 0.19/0.57             (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.19/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.57  thf('8', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         ((r2_hidden @ 
% 0.19/0.57           (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.57  thf('9', plain,
% 0.19/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57         | (r2_hidden @ 
% 0.19/0.57            (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.19/0.57            sk_B_1)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['4', '8'])).
% 0.19/0.57  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('11', plain,
% 0.19/0.57      (((r2_hidden @ 
% 0.19/0.57         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.19/0.57         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.57  thf(t204_relat_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ C ) =>
% 0.19/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.57         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.57  thf('12', plain,
% 0.19/0.57      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.19/0.57         (~ (r2_hidden @ (k4_tarski @ X50 @ X48) @ X49)
% 0.19/0.57          | (r2_hidden @ X48 @ (k11_relat_1 @ X49 @ X50))
% 0.19/0.57          | ~ (v1_relat_1 @ X49))),
% 0.19/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.57  thf('13', plain,
% 0.19/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.57  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('15', plain,
% 0.19/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57         (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.57  thf('16', plain,
% 0.19/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57         k1_xboole_0))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup+', [status(thm)], ['2', '15'])).
% 0.19/0.57  thf('17', plain,
% 0.19/0.57      (((r2_hidden @ 
% 0.19/0.57         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.19/0.57         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.57  thf('18', plain,
% 0.19/0.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X43 @ X44)
% 0.19/0.57          | ~ (r2_hidden @ (k4_tarski @ X45 @ X43) @ X46)
% 0.19/0.57          | ~ (r2_hidden @ X43 @ (k2_relat_1 @ X46))
% 0.19/0.57          | (r2_hidden @ X45 @ (k10_relat_1 @ X46 @ X44))
% 0.19/0.57          | ~ (v1_relat_1 @ X46))),
% 0.19/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.57  thf('19', plain,
% 0.19/0.57      ((![X0 : $i]:
% 0.19/0.57          (~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57           | (r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.19/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57                (k2_relat_1 @ sk_B_1))
% 0.19/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.57  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('21', plain,
% 0.19/0.57      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('split', [status(esa)], ['3'])).
% 0.19/0.57  thf('22', plain,
% 0.19/0.57      (![X47 : $i]:
% 0.19/0.57         (((k10_relat_1 @ X47 @ (k2_relat_1 @ X47)) = (k1_relat_1 @ X47))
% 0.19/0.57          | ~ (v1_relat_1 @ X47))),
% 0.19/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.57  thf('23', plain,
% 0.19/0.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X45 @ (k10_relat_1 @ X46 @ X44))
% 0.19/0.57          | (r2_hidden @ (sk_D @ X46 @ X44 @ X45) @ X44)
% 0.19/0.57          | ~ (v1_relat_1 @ X46))),
% 0.19/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.57  thf('24', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | (r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.19/0.57             (k2_relat_1 @ X0)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.57  thf('25', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         ((r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ (k2_relat_1 @ X0))
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.57  thf('26', plain,
% 0.19/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57            (k2_relat_1 @ sk_B_1))))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['21', '25'])).
% 0.19/0.57  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('28', plain,
% 0.19/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.19/0.57         (k2_relat_1 @ sk_B_1)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.57  thf('29', plain,
% 0.19/0.57      ((![X0 : $i]:
% 0.19/0.57          ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ X0))
% 0.19/0.57           | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ X0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['19', '20', '28'])).
% 0.19/0.57  thf('30', plain,
% 0.19/0.57      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_B_1 @ k1_xboole_0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['16', '29'])).
% 0.19/0.57  thf('31', plain,
% 0.19/0.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X45 @ (k10_relat_1 @ X46 @ X44))
% 0.19/0.57          | (r2_hidden @ (sk_D @ X46 @ X44 @ X45) @ X44)
% 0.19/0.57          | ~ (v1_relat_1 @ X46))),
% 0.19/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.57  thf('32', plain,
% 0.19/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57         | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.57  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('34', plain,
% 0.19/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.57  thf(l1_zfmisc_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.57  thf('35', plain,
% 0.19/0.57      (![X33 : $i, X35 : $i]:
% 0.19/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.19/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.57  thf('36', plain,
% 0.19/0.57      (((r1_tarski @ (k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) @ 
% 0.19/0.57         k1_xboole_0))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.57  thf(t3_xboole_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.57  thf('37', plain,
% 0.19/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.57  thf('38', plain,
% 0.19/0.57      ((((k1_tarski @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A)) = (k1_xboole_0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.57  thf(t20_zfmisc_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.57         ( k1_tarski @ A ) ) <=>
% 0.19/0.57       ( ( A ) != ( B ) ) ))).
% 0.19/0.57  thf('39', plain,
% 0.19/0.57      (![X38 : $i, X39 : $i]:
% 0.19/0.57         (((X39) != (X38))
% 0.19/0.57          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.19/0.57              != (k1_tarski @ X39)))),
% 0.19/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.57  thf('40', plain,
% 0.19/0.57      (![X38 : $i]:
% 0.19/0.57         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.19/0.57           != (k1_tarski @ X38))),
% 0.19/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.57  thf(t69_enumset1, axiom,
% 0.19/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.57  thf('41', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.19/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.57  thf(t19_zfmisc_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.19/0.57       ( k1_tarski @ A ) ))).
% 0.19/0.57  thf('42', plain,
% 0.19/0.57      (![X36 : $i, X37 : $i]:
% 0.19/0.57         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.19/0.57           = (k1_tarski @ X36))),
% 0.19/0.57      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.19/0.57  thf('43', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.19/0.57           = (k1_tarski @ X0))),
% 0.19/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.19/0.57  thf('44', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.19/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.57  thf(t12_setfam_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.57  thf('45', plain,
% 0.19/0.57      (![X41 : $i, X42 : $i]:
% 0.19/0.57         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.19/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.57  thf('46', plain,
% 0.19/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.19/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.19/0.57  thf('47', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.19/0.57      inference('demod', [status(thm)], ['43', '46'])).
% 0.19/0.57  thf('48', plain,
% 0.19/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.19/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.19/0.57  thf(t100_xboole_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.57  thf('49', plain,
% 0.19/0.57      (![X1 : $i, X2 : $i]:
% 0.19/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.19/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((k4_xboole_0 @ X0 @ X0)
% 0.19/0.57           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.19/0.57      inference('sup+', [status(thm)], ['48', '49'])).
% 0.19/0.57  thf('51', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.19/0.57           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.19/0.57      inference('sup+', [status(thm)], ['47', '50'])).
% 0.19/0.57  thf(t92_xboole_1, axiom,
% 0.19/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.57  thf('52', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.57  thf('53', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.19/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.57  thf('54', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.19/0.57      inference('demod', [status(thm)], ['40', '53'])).
% 0.19/0.57  thf('55', plain,
% 0.19/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.57         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.57             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['38', '54'])).
% 0.19/0.57  thf('56', plain,
% 0.19/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.57       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.57  thf('57', plain,
% 0.19/0.57      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('split', [status(esa)], ['3'])).
% 0.19/0.57  thf(t7_xboole_0, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.57  thf('58', plain,
% 0.19/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.57  thf('59', plain,
% 0.19/0.57      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X48 @ (k11_relat_1 @ X49 @ X50))
% 0.19/0.57          | (r2_hidden @ (k4_tarski @ X50 @ X48) @ X49)
% 0.19/0.57          | ~ (v1_relat_1 @ X49))),
% 0.19/0.57      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.57  thf('60', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.57          | ~ (v1_relat_1 @ X1)
% 0.19/0.57          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.19/0.57             X1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.57  thf(t20_relat_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ C ) =>
% 0.19/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.19/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.57           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.19/0.57  thf('61', plain,
% 0.19/0.57      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.19/0.57         (~ (r2_hidden @ (k4_tarski @ X51 @ X52) @ X53)
% 0.19/0.57          | (r2_hidden @ X51 @ (k1_relat_1 @ X53))
% 0.19/0.57          | ~ (v1_relat_1 @ X53))),
% 0.19/0.57      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.19/0.57  thf('62', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (v1_relat_1 @ X0)
% 0.19/0.57          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.57  thf('63', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.19/0.57          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.57          | ~ (v1_relat_1 @ X0))),
% 0.19/0.57      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.57  thf('64', plain,
% 0.19/0.57      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.19/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('split', [status(esa)], ['0'])).
% 0.19/0.57  thf('65', plain,
% 0.19/0.57      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57         | ((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.19/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.57  thf('66', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('67', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.19/0.57         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.19/0.57  thf('68', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.19/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.57      inference('split', [status(esa)], ['3'])).
% 0.19/0.57  thf('69', plain,
% 0.19/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.57         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.57             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.57  thf('70', plain,
% 0.19/0.57      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.57       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['69'])).
% 0.19/0.57  thf('71', plain, ($false),
% 0.19/0.57      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '70'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
