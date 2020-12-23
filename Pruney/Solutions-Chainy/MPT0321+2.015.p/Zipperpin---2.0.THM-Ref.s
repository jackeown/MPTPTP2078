%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FYerU0GqM7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:35 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 925 expanded)
%              Number of leaves         :   22 ( 302 expanded)
%              Depth                    :   25
%              Number of atoms          : 1181 (9618 expanded)
%              Number of equality atoms :  168 (1439 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X30 @ X32 ) @ ( k3_xboole_0 @ X31 @ X33 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X30 @ X32 ) @ ( k3_xboole_0 @ X31 @ X33 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( ( k4_xboole_0 @ X15 @ X14 )
       != ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
     != k1_xboole_0 )
    | ( sk_C_1 = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k4_xboole_0 @ X34 @ X36 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k4_xboole_0 @ X34 @ X36 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_B_1
      = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_B_1 = sk_D ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X30 @ X32 ) @ ( k3_xboole_0 @ X31 @ X33 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['78','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('91',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('95',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('97',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    r1_tarski @ sk_B_1 @ sk_D ),
    inference(demod,[status(thm)],['101','103'])).

thf('105',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['72','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('107',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('108',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','105','106','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = sk_A ) ),
    inference(demod,[status(thm)],['38','110'])).

thf('112',plain,(
    sk_C_1 = sk_A ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['72','104'])).

thf('116',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['113'])).

thf('117',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_B_1 = sk_D ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['113'])).

thf('120',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['114','120'])).

thf('122',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FYerU0GqM7
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 1397 iterations in 0.552s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.77/1.01  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/1.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.01  thf(t3_boole, axiom,
% 0.77/1.01    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/1.01  thf('0', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.77/1.01      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/1.01  thf(t48_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('1', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('2', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['0', '1'])).
% 0.77/1.01  thf(t2_boole, axiom,
% 0.77/1.01    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.77/1.01  thf('3', plain,
% 0.77/1.01      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.77/1.01  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('demod', [status(thm)], ['2', '3'])).
% 0.77/1.01  thf('5', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('6', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['4', '5'])).
% 0.77/1.01  thf('7', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.77/1.01      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/1.01  thf('8', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf(t134_zfmisc_1, conjecture,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.01         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/1.01          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.01            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.77/1.01  thf('9', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t125_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.77/1.01         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.77/1.01       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.77/1.01         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.77/1.01  thf('10', plain,
% 0.77/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('11', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.77/1.01              (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/1.01  thf('12', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('13', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.77/1.01           (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.77/1.01              (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['11', '12'])).
% 0.77/1.01  thf('14', plain,
% 0.77/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('15', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf(t123_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.77/1.01       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.77/1.01  thf('16', plain,
% 0.77/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X30 @ X32) @ (k3_xboole_0 @ X31 @ X33))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X32 @ X33)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.77/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/1.01  thf('17', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('18', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 0.77/1.01           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_C_1) @ 
% 0.77/1.01              (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.77/1.01  thf('19', plain,
% 0.77/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X30 @ X32) @ (k3_xboole_0 @ X31 @ X33))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X32 @ X33)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.77/1.01  thf('20', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf(t36_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.77/1.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.77/1.01  thf(l32_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      (![X10 : $i, X12 : $i]:
% 0.77/1.01         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.77/1.01          | ~ (r1_tarski @ X10 @ X12))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('24', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/1.01  thf('25', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['21', '24'])).
% 0.77/1.01  thf('26', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['20', '25'])).
% 0.77/1.01  thf('27', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ 
% 0.77/1.01           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.77/1.01           (k2_zfmisc_1 @ X2 @ X0)) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['19', '26'])).
% 0.77/1.01  thf('28', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1) @ 
% 0.77/1.01           (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['18', '27'])).
% 0.77/1.01  thf('29', plain,
% 0.77/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('30', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_1) @ 
% 0.77/1.01           sk_B_1) = (k1_xboole_0))),
% 0.77/1.01      inference('demod', [status(thm)], ['28', '29'])).
% 0.77/1.01  thf('31', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['8', '30'])).
% 0.77/1.01  thf(t113_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      (![X24 : $i, X25 : $i]:
% 0.77/1.01         (((X24) = (k1_xboole_0))
% 0.77/1.01          | ((X25) = (k1_xboole_0))
% 0.77/1.01          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('33', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.77/1.01        | ((sk_B_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/1.01  thf('34', plain,
% 0.77/1.01      ((((sk_B_1) = (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['33'])).
% 0.77/1.01  thf('35', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('36', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.77/1.01  thf(t32_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.77/1.01       ( ( A ) = ( B ) ) ))).
% 0.77/1.01  thf('37', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         (((X15) = (X14))
% 0.77/1.01          | ((k4_xboole_0 @ X15 @ X14) != (k4_xboole_0 @ X14 @ X15)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.77/1.01  thf('38', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_C_1 @ sk_A) != (k1_xboole_0)) | ((sk_C_1) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.77/1.01              (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/1.01  thf('40', plain,
% 0.77/1.01      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ X37 @ (k4_xboole_0 @ X34 @ X36))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('41', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_D))
% 0.77/1.01         = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.77/1.01      inference('sup+', [status(thm)], ['39', '40'])).
% 0.77/1.01  thf('42', plain,
% 0.77/1.01      (![X24 : $i, X25 : $i]:
% 0.77/1.01         (((X24) = (k1_xboole_0))
% 0.77/1.01          | ((X25) = (k1_xboole_0))
% 0.77/1.01          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('43', plain,
% 0.77/1.01      ((((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_D))
% 0.77/1.01          != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 0.77/1.01        | ((sk_B_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/1.01  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('45', plain,
% 0.77/1.01      ((((k2_zfmisc_1 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_D))
% 0.77/1.01          != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.77/1.01  thf('46', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('47', plain,
% 0.77/1.01      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ X37 @ (k4_xboole_0 @ X34 @ X36))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('48', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.77/1.01              (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['46', '47'])).
% 0.77/1.01  thf('49', plain,
% 0.77/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('50', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D)
% 0.77/1.01         = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['48', '49'])).
% 0.77/1.01  thf('51', plain,
% 0.77/1.01      (![X24 : $i, X25 : $i]:
% 0.77/1.01         (((X24) = (k1_xboole_0))
% 0.77/1.01          | ((X25) = (k1_xboole_0))
% 0.77/1.01          | ((k2_zfmisc_1 @ X25 @ X24) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('52', plain,
% 0.77/1.01      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D) != (k1_xboole_0))
% 0.77/1.01        | ((sk_A) = (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.77/1.01  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('54', plain,
% 0.77/1.01      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D) != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.77/1.01  thf('55', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.77/1.01  thf('56', plain,
% 0.77/1.01      (![X25 : $i, X26 : $i]:
% 0.77/1.01         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.77/1.01          | ((X25) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('57', plain,
% 0.77/1.01      (![X26 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['56'])).
% 0.77/1.01  thf('58', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['54', '55', '57'])).
% 0.77/1.01  thf('59', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['58'])).
% 0.77/1.01  thf('60', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('61', plain,
% 0.77/1.01      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.77/1.01  thf('62', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.77/1.01      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/1.01  thf('63', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.77/1.01  thf('64', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['20', '25'])).
% 0.77/1.01  thf('65', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i]:
% 0.77/1.01         ((r1_tarski @ X10 @ X11)
% 0.77/1.01          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('66', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('67', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.77/1.01      inference('simplify', [status(thm)], ['66'])).
% 0.77/1.01  thf(d10_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/1.01  thf('68', plain,
% 0.77/1.01      (![X7 : $i, X9 : $i]:
% 0.77/1.01         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.01  thf('69', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/1.01  thf('70', plain,
% 0.77/1.01      ((~ (r1_tarski @ sk_B_1 @ sk_D)
% 0.77/1.01        | ((sk_B_1) = (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['63', '69'])).
% 0.77/1.01  thf('71', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.77/1.01  thf('72', plain, ((~ (r1_tarski @ sk_B_1 @ sk_D) | ((sk_B_1) = (sk_D)))),
% 0.77/1.01      inference('demod', [status(thm)], ['70', '71'])).
% 0.77/1.01  thf('73', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.77/1.01  thf('74', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('75', plain,
% 0.77/1.01      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/1.01      inference('sup+', [status(thm)], ['73', '74'])).
% 0.77/1.01  thf('76', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.77/1.01      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/1.01  thf('77', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('78', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.77/1.01  thf('79', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('80', plain,
% 0.77/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('81', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['79', '80'])).
% 0.77/1.01  thf('82', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('83', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.01           (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['81', '82'])).
% 0.77/1.01  thf('84', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['79', '80'])).
% 0.77/1.01  thf('85', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ X19 @ X20))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('86', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.77/1.01      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.77/1.01  thf('87', plain,
% 0.77/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X30 @ X32) @ (k3_xboole_0 @ X31 @ X33))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X32 @ X33)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.77/1.01  thf('88', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.77/1.01           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ 
% 0.77/1.01              (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('demod', [status(thm)], ['86', '87'])).
% 0.77/1.01  thf('89', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B_1)
% 0.77/1.01         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['78', '88'])).
% 0.77/1.01  thf('90', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('91', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 0.77/1.01         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('demod', [status(thm)], ['89', '90'])).
% 0.77/1.01  thf('92', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('93', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_C_1 @ sk_D)
% 0.77/1.01         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.77/1.01      inference('demod', [status(thm)], ['91', '92'])).
% 0.77/1.01  thf('94', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.77/1.01  thf('95', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_C_1 @ sk_D) = (k2_zfmisc_1 @ sk_A @ sk_D))),
% 0.77/1.01      inference('demod', [status(thm)], ['93', '94'])).
% 0.77/1.01  thf('96', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t117_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/1.01          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.77/1.01            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.77/1.01          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.77/1.01  thf('97', plain,
% 0.77/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.77/1.01         (((X27) = (k1_xboole_0))
% 0.77/1.01          | (r1_tarski @ X28 @ X29)
% 0.77/1.01          | ~ (r1_tarski @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 0.77/1.01               (k2_zfmisc_1 @ X27 @ X29)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.77/1.01  thf('98', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.02             (k2_zfmisc_1 @ sk_A @ X0))
% 0.77/1.02          | (r1_tarski @ sk_B_1 @ X0)
% 0.77/1.02          | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/1.02  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('100', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.02             (k2_zfmisc_1 @ sk_A @ X0))
% 0.77/1.02          | (r1_tarski @ sk_B_1 @ X0))),
% 0.77/1.02      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 0.77/1.02  thf('101', plain,
% 0.77/1.02      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.77/1.02           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.77/1.02        | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.77/1.02      inference('sup-', [status(thm)], ['95', '100'])).
% 0.77/1.02  thf('102', plain,
% 0.77/1.02      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.77/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.02  thf('103', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.77/1.02      inference('simplify', [status(thm)], ['102'])).
% 0.77/1.02  thf('104', plain, ((r1_tarski @ sk_B_1 @ sk_D)),
% 0.77/1.02      inference('demod', [status(thm)], ['101', '103'])).
% 0.77/1.02  thf('105', plain, (((sk_B_1) = (sk_D))),
% 0.77/1.02      inference('demod', [status(thm)], ['72', '104'])).
% 0.77/1.02  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.02      inference('demod', [status(thm)], ['2', '3'])).
% 0.77/1.02  thf('107', plain,
% 0.77/1.02      (![X25 : $i, X26 : $i]:
% 0.77/1.02         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.77/1.02          | ((X26) != (k1_xboole_0)))),
% 0.77/1.02      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.02  thf('108', plain,
% 0.77/1.02      (![X25 : $i]: ((k2_zfmisc_1 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['107'])).
% 0.77/1.02  thf('109', plain,
% 0.77/1.02      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.02        | ((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 0.77/1.02      inference('demod', [status(thm)], ['45', '105', '106', '108'])).
% 0.77/1.02  thf('110', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['109'])).
% 0.77/1.02  thf('111', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (sk_A)))),
% 0.77/1.02      inference('demod', [status(thm)], ['38', '110'])).
% 0.77/1.02  thf('112', plain, (((sk_C_1) = (sk_A))),
% 0.77/1.02      inference('simplify', [status(thm)], ['111'])).
% 0.77/1.02  thf('113', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('114', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.77/1.02      inference('split', [status(esa)], ['113'])).
% 0.77/1.02  thf('115', plain, (((sk_B_1) = (sk_D))),
% 0.77/1.02      inference('demod', [status(thm)], ['72', '104'])).
% 0.77/1.02  thf('116', plain, ((((sk_B_1) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.77/1.02      inference('split', [status(esa)], ['113'])).
% 0.77/1.02  thf('117', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['115', '116'])).
% 0.77/1.02  thf('118', plain, ((((sk_B_1) = (sk_D)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['117'])).
% 0.77/1.02  thf('119', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B_1) = (sk_D)))),
% 0.77/1.02      inference('split', [status(esa)], ['113'])).
% 0.77/1.02  thf('120', plain, (~ (((sk_A) = (sk_C_1)))),
% 0.77/1.02      inference('sat_resolution*', [status(thm)], ['118', '119'])).
% 0.77/1.02  thf('121', plain, (((sk_A) != (sk_C_1))),
% 0.77/1.02      inference('simpl_trail', [status(thm)], ['114', '120'])).
% 0.77/1.02  thf('122', plain, ($false),
% 0.77/1.02      inference('simplify_reflect-', [status(thm)], ['112', '121'])).
% 0.77/1.02  
% 0.77/1.02  % SZS output end Refutation
% 0.77/1.02  
% 0.77/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
