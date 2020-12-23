%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzxiUYrd7d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 193 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  806 (1658 expanded)
%              Number of equality atoms :  108 ( 220 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X34 @ X33 ) @ X33 )
      | ( X33
        = ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X58 @ X57 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X58 @ X56 ) @ X58 ) @ X56 )
      | ( X57
       != ( k2_relat_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X56: $i,X58: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X58 @ X56 ) @ X58 ) @ X56 )
      | ~ ( r2_hidden @ X58 @ ( k2_relat_1 @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('4',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X32 ) )
      = ( k1_tarski @ ( k4_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k1_tarski @ ( k4_tarski @ X26 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_4 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_C_4 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
      | ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) )
      | ( X24 != X25 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('13',plain,(
    ! [X25: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X54 @ X55 ) @ X56 )
      | ( r2_hidden @ X55 @ X57 )
      | ( X57
       != ( k2_relat_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('17',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ ( k2_relat_1 @ X56 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X54 @ X55 ) @ X56 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X16 )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_relat_1 @ sk_C_4 ) )
    = ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_B ) )
    = ( k2_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('24',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_C_4 ) )
        = sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( ( sk_C_1 @ X34 @ X33 )
       != X34 )
      | ( X33
        = ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( ( k2_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X34 @ X33 ) @ X33 )
      | ( X33
        = ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X51 @ X50 )
      | ( r2_hidden @ ( k4_tarski @ X51 @ ( sk_D_2 @ X51 @ X49 ) ) @ X49 )
      | ( X50
       != ( k1_relat_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('35',plain,(
    ! [X49: $i,X51: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X51 @ ( sk_D_2 @ X51 @ X49 ) ) @ X49 )
      | ~ ( r2_hidden @ X51 @ ( k1_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 = X26 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X32 ) )
      = ( k1_tarski @ ( k4_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_4 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_4 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['10','14'])).

thf('50',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ X49 )
      | ( r2_hidden @ X47 @ X50 )
      | ( X50
       != ( k1_relat_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('51',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ X47 @ ( k1_relat_1 @ X49 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ X49 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X16 )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) )
    = ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('58',plain,(
    ( k1_relat_1 @ sk_C_4 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_4 ) )
        = sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( ( sk_C_1 @ X34 @ X33 )
       != X34 )
      | ( X33
        = ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( k1_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_4 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ( k1_relat_1 @ sk_C_4 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_relat_1 @ sk_C_4 ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['32','69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzxiUYrd7d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.32/3.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.32/3.56  % Solved by: fo/fo7.sh
% 3.32/3.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.32/3.56  % done 4758 iterations in 3.113s
% 3.32/3.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.32/3.56  % SZS output start Refutation
% 3.32/3.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.32/3.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.32/3.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.32/3.56  thf(sk_B_type, type, sk_B: $i).
% 3.32/3.56  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 3.32/3.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.32/3.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.32/3.56  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 3.32/3.56  thf(sk_A_type, type, sk_A: $i).
% 3.32/3.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.32/3.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.32/3.56  thf(sk_C_4_type, type, sk_C_4: $i).
% 3.32/3.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.32/3.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.32/3.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.32/3.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.32/3.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.32/3.56  thf(t41_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.32/3.56          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 3.32/3.56  thf('0', plain,
% 3.32/3.56      (![X33 : $i, X34 : $i]:
% 3.32/3.56         (((X33) = (k1_xboole_0))
% 3.32/3.56          | (r2_hidden @ (sk_C_1 @ X34 @ X33) @ X33)
% 3.32/3.56          | ((X33) = (k1_tarski @ X34)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 3.32/3.56  thf(d5_relat_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.32/3.56       ( ![C:$i]:
% 3.32/3.56         ( ( r2_hidden @ C @ B ) <=>
% 3.32/3.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.32/3.56  thf('1', plain,
% 3.32/3.56      (![X56 : $i, X57 : $i, X58 : $i]:
% 3.32/3.56         (~ (r2_hidden @ X58 @ X57)
% 3.32/3.56          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X58 @ X56) @ X58) @ X56)
% 3.32/3.56          | ((X57) != (k2_relat_1 @ X56)))),
% 3.32/3.56      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.32/3.56  thf('2', plain,
% 3.32/3.56      (![X56 : $i, X58 : $i]:
% 3.32/3.56         ((r2_hidden @ (k4_tarski @ (sk_D_4 @ X58 @ X56) @ X58) @ X56)
% 3.32/3.56          | ~ (r2_hidden @ X58 @ (k2_relat_1 @ X56)))),
% 3.32/3.56      inference('simplify', [status(thm)], ['1'])).
% 3.32/3.56  thf('3', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]:
% 3.32/3.56         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 3.32/3.56          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.32/3.56          | (r2_hidden @ 
% 3.32/3.56             (k4_tarski @ (sk_D_4 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.32/3.56              (sk_C_1 @ X1 @ (k2_relat_1 @ X0))) @ 
% 3.32/3.56             X0))),
% 3.32/3.56      inference('sup-', [status(thm)], ['0', '2'])).
% 3.32/3.56  thf(t23_relat_1, conjecture,
% 3.32/3.56    (![A:$i,B:$i,C:$i]:
% 3.32/3.56     ( ( v1_relat_1 @ C ) =>
% 3.32/3.56       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.32/3.56         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.32/3.56           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 3.32/3.56  thf(zf_stmt_0, negated_conjecture,
% 3.32/3.56    (~( ![A:$i,B:$i,C:$i]:
% 3.32/3.56        ( ( v1_relat_1 @ C ) =>
% 3.32/3.56          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.32/3.56            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.32/3.56              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 3.32/3.56    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 3.32/3.56  thf('4', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.32/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.56  thf(t34_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.56     ( ( r2_hidden @
% 3.32/3.56         ( k4_tarski @ A @ B ) @ 
% 3.32/3.56         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 3.32/3.56       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 3.32/3.56  thf('5', plain,
% 3.32/3.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.32/3.56         (((X28) = (X29))
% 3.32/3.56          | ~ (r2_hidden @ (k4_tarski @ X27 @ X28) @ 
% 3.32/3.56               (k2_zfmisc_1 @ (k1_tarski @ X26) @ (k1_tarski @ X29))))),
% 3.32/3.56      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 3.32/3.56  thf(t35_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 3.32/3.56       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 3.32/3.56  thf('6', plain,
% 3.32/3.56      (![X31 : $i, X32 : $i]:
% 3.32/3.56         ((k2_zfmisc_1 @ (k1_tarski @ X31) @ (k1_tarski @ X32))
% 3.32/3.56           = (k1_tarski @ (k4_tarski @ X31 @ X32)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 3.32/3.56  thf('7', plain,
% 3.32/3.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.32/3.56         (((X28) = (X29))
% 3.32/3.56          | ~ (r2_hidden @ (k4_tarski @ X27 @ X28) @ 
% 3.32/3.56               (k1_tarski @ (k4_tarski @ X26 @ X29))))),
% 3.32/3.56      inference('demod', [status(thm)], ['5', '6'])).
% 3.32/3.56  thf('8', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]:
% 3.32/3.56         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X0) = (sk_B)))),
% 3.32/3.56      inference('sup-', [status(thm)], ['4', '7'])).
% 3.32/3.56  thf('9', plain,
% 3.32/3.56      (![X0 : $i]:
% 3.32/3.56         (((k2_relat_1 @ sk_C_4) = (k1_xboole_0))
% 3.32/3.56          | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.56          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_C_4)) = (sk_B)))),
% 3.32/3.56      inference('sup-', [status(thm)], ['3', '8'])).
% 3.32/3.56  thf('10', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.32/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.56  thf(l27_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.32/3.56  thf('11', plain,
% 3.32/3.56      (![X18 : $i, X19 : $i]:
% 3.32/3.56         ((r1_xboole_0 @ (k1_tarski @ X18) @ X19) | (r2_hidden @ X18 @ X19))),
% 3.32/3.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.32/3.56  thf(t16_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 3.32/3.56          ( ( A ) = ( B ) ) ) ))).
% 3.32/3.56  thf('12', plain,
% 3.32/3.56      (![X24 : $i, X25 : $i]:
% 3.32/3.56         (~ (r1_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25))
% 3.32/3.56          | ((X24) != (X25)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 3.32/3.56  thf('13', plain,
% 3.32/3.56      (![X25 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))),
% 3.32/3.56      inference('simplify', [status(thm)], ['12'])).
% 3.32/3.56  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.32/3.56      inference('sup-', [status(thm)], ['11', '13'])).
% 3.32/3.56  thf('15', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_4)),
% 3.32/3.56      inference('sup+', [status(thm)], ['10', '14'])).
% 3.32/3.56  thf('16', plain,
% 3.32/3.56      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 3.32/3.56         (~ (r2_hidden @ (k4_tarski @ X54 @ X55) @ X56)
% 3.32/3.56          | (r2_hidden @ X55 @ X57)
% 3.32/3.56          | ((X57) != (k2_relat_1 @ X56)))),
% 3.32/3.56      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.32/3.56  thf('17', plain,
% 3.32/3.56      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.32/3.56         ((r2_hidden @ X55 @ (k2_relat_1 @ X56))
% 3.32/3.56          | ~ (r2_hidden @ (k4_tarski @ X54 @ X55) @ X56))),
% 3.32/3.56      inference('simplify', [status(thm)], ['16'])).
% 3.32/3.56  thf('18', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_4))),
% 3.32/3.56      inference('sup-', [status(thm)], ['15', '17'])).
% 3.32/3.56  thf(l22_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( r2_hidden @ A @ B ) =>
% 3.32/3.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 3.32/3.56  thf('19', plain,
% 3.32/3.56      (![X16 : $i, X17 : $i]:
% 3.32/3.56         (((k2_xboole_0 @ (k1_tarski @ X17) @ X16) = (X16))
% 3.32/3.56          | ~ (r2_hidden @ X17 @ X16))),
% 3.32/3.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 3.32/3.56  thf('20', plain,
% 3.32/3.56      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k2_relat_1 @ sk_C_4))
% 3.32/3.56         = (k2_relat_1 @ sk_C_4))),
% 3.32/3.56      inference('sup-', [status(thm)], ['18', '19'])).
% 3.32/3.56  thf(commutativity_k2_xboole_0, axiom,
% 3.32/3.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.32/3.56  thf('21', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.32/3.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.32/3.56  thf('22', plain,
% 3.32/3.56      (((k2_xboole_0 @ (k2_relat_1 @ sk_C_4) @ (k1_tarski @ sk_B))
% 3.32/3.56         = (k2_relat_1 @ sk_C_4))),
% 3.32/3.56      inference('demod', [status(thm)], ['20', '21'])).
% 3.32/3.56  thf('23', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.32/3.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.32/3.56  thf(t49_zfmisc_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 3.32/3.56  thf('24', plain,
% 3.32/3.56      (![X38 : $i, X39 : $i]:
% 3.32/3.56         ((k2_xboole_0 @ (k1_tarski @ X38) @ X39) != (k1_xboole_0))),
% 3.32/3.56      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 3.32/3.56  thf('25', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]:
% 3.32/3.56         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 3.32/3.56      inference('sup-', [status(thm)], ['23', '24'])).
% 3.32/3.56  thf('26', plain, (((k2_relat_1 @ sk_C_4) != (k1_xboole_0))),
% 3.32/3.56      inference('sup-', [status(thm)], ['22', '25'])).
% 3.32/3.56  thf('27', plain,
% 3.32/3.56      (![X0 : $i]:
% 3.32/3.56         (((k2_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.56          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_C_4)) = (sk_B)))),
% 3.32/3.56      inference('simplify_reflect-', [status(thm)], ['9', '26'])).
% 3.32/3.56  thf('28', plain,
% 3.32/3.56      (![X33 : $i, X34 : $i]:
% 3.32/3.56         (((X33) = (k1_xboole_0))
% 3.32/3.56          | ((sk_C_1 @ X34 @ X33) != (X34))
% 3.32/3.56          | ((X33) = (k1_tarski @ X34)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 3.32/3.56  thf('29', plain,
% 3.32/3.56      (![X0 : $i]:
% 3.32/3.56         (((sk_B) != (X0))
% 3.32/3.56          | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.56          | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.56          | ((k2_relat_1 @ sk_C_4) = (k1_xboole_0)))),
% 3.32/3.56      inference('sup-', [status(thm)], ['27', '28'])).
% 3.32/3.56  thf('30', plain,
% 3.32/3.56      ((((k2_relat_1 @ sk_C_4) = (k1_xboole_0))
% 3.32/3.56        | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 3.32/3.56      inference('simplify', [status(thm)], ['29'])).
% 3.32/3.56  thf('31', plain,
% 3.32/3.56      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A))
% 3.32/3.56        | ((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))),
% 3.32/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.56  thf('32', plain,
% 3.32/3.56      ((((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))
% 3.32/3.56         <= (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))))),
% 3.32/3.56      inference('split', [status(esa)], ['31'])).
% 3.32/3.56  thf('33', plain,
% 3.32/3.56      (![X33 : $i, X34 : $i]:
% 3.32/3.56         (((X33) = (k1_xboole_0))
% 3.32/3.56          | (r2_hidden @ (sk_C_1 @ X34 @ X33) @ X33)
% 3.32/3.56          | ((X33) = (k1_tarski @ X34)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 3.32/3.56  thf(d4_relat_1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.32/3.56       ( ![C:$i]:
% 3.32/3.56         ( ( r2_hidden @ C @ B ) <=>
% 3.32/3.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.32/3.56  thf('34', plain,
% 3.32/3.56      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.32/3.56         (~ (r2_hidden @ X51 @ X50)
% 3.32/3.56          | (r2_hidden @ (k4_tarski @ X51 @ (sk_D_2 @ X51 @ X49)) @ X49)
% 3.32/3.56          | ((X50) != (k1_relat_1 @ X49)))),
% 3.32/3.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.32/3.56  thf('35', plain,
% 3.32/3.56      (![X49 : $i, X51 : $i]:
% 3.32/3.56         ((r2_hidden @ (k4_tarski @ X51 @ (sk_D_2 @ X51 @ X49)) @ X49)
% 3.32/3.56          | ~ (r2_hidden @ X51 @ (k1_relat_1 @ X49)))),
% 3.32/3.56      inference('simplify', [status(thm)], ['34'])).
% 3.32/3.56  thf('36', plain,
% 3.32/3.56      (![X0 : $i, X1 : $i]:
% 3.32/3.56         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 3.32/3.56          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 3.32/3.56          | (r2_hidden @ 
% 3.32/3.56             (k4_tarski @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.32/3.56              (sk_D_2 @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 3.32/3.56             X0))),
% 3.32/3.56      inference('sup-', [status(thm)], ['33', '35'])).
% 3.32/3.56  thf('37', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.32/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.56  thf(t41_enumset1, axiom,
% 3.32/3.56    (![A:$i,B:$i]:
% 3.32/3.56     ( ( k2_tarski @ A @ B ) =
% 3.32/3.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 3.32/3.56  thf('38', plain,
% 3.32/3.56      (![X14 : $i, X15 : $i]:
% 3.32/3.56         ((k2_tarski @ X14 @ X15)
% 3.32/3.56           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 3.32/3.56      inference('cnf', [status(esa)], [t41_enumset1])).
% 3.32/3.56  thf(idempotence_k2_xboole_0, axiom,
% 3.32/3.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 3.32/3.56  thf('39', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 3.32/3.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.32/3.57  thf('40', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 3.32/3.57      inference('sup+', [status(thm)], ['38', '39'])).
% 3.32/3.57  thf('41', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 3.32/3.57      inference('sup+', [status(thm)], ['38', '39'])).
% 3.32/3.57  thf('42', plain,
% 3.32/3.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.32/3.57         (((X27) = (X26))
% 3.32/3.57          | ~ (r2_hidden @ (k4_tarski @ X27 @ X28) @ 
% 3.32/3.57               (k2_zfmisc_1 @ (k1_tarski @ X26) @ (k1_tarski @ X29))))),
% 3.32/3.57      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 3.32/3.57  thf('43', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.57         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.32/3.57             (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 3.32/3.57          | ((X3) = (X1)))),
% 3.32/3.57      inference('sup-', [status(thm)], ['41', '42'])).
% 3.32/3.57  thf('44', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.57         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.32/3.57             (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 3.32/3.57          | ((X3) = (X1)))),
% 3.32/3.57      inference('sup-', [status(thm)], ['40', '43'])).
% 3.32/3.57  thf('45', plain,
% 3.32/3.57      (![X31 : $i, X32 : $i]:
% 3.32/3.57         ((k2_zfmisc_1 @ (k1_tarski @ X31) @ (k1_tarski @ X32))
% 3.32/3.57           = (k1_tarski @ (k4_tarski @ X31 @ X32)))),
% 3.32/3.57      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 3.32/3.57  thf('46', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.57         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.32/3.57             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.32/3.57          | ((X3) = (X1)))),
% 3.32/3.57      inference('demod', [status(thm)], ['44', '45'])).
% 3.32/3.57  thf('47', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i]:
% 3.32/3.57         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X1) = (sk_A)))),
% 3.32/3.57      inference('sup-', [status(thm)], ['37', '46'])).
% 3.32/3.57  thf('48', plain,
% 3.32/3.57      (![X0 : $i]:
% 3.32/3.57         (((k1_relat_1 @ sk_C_4) = (k1_xboole_0))
% 3.32/3.57          | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.57          | ((sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_4)) = (sk_A)))),
% 3.32/3.57      inference('sup-', [status(thm)], ['36', '47'])).
% 3.32/3.57  thf('49', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_4)),
% 3.32/3.57      inference('sup+', [status(thm)], ['10', '14'])).
% 3.32/3.57  thf('50', plain,
% 3.32/3.57      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 3.32/3.57         (~ (r2_hidden @ (k4_tarski @ X47 @ X48) @ X49)
% 3.32/3.57          | (r2_hidden @ X47 @ X50)
% 3.32/3.57          | ((X50) != (k1_relat_1 @ X49)))),
% 3.32/3.57      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.32/3.57  thf('51', plain,
% 3.32/3.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.32/3.57         ((r2_hidden @ X47 @ (k1_relat_1 @ X49))
% 3.32/3.57          | ~ (r2_hidden @ (k4_tarski @ X47 @ X48) @ X49))),
% 3.32/3.57      inference('simplify', [status(thm)], ['50'])).
% 3.32/3.57  thf('52', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_4))),
% 3.32/3.57      inference('sup-', [status(thm)], ['49', '51'])).
% 3.32/3.57  thf('53', plain,
% 3.32/3.57      (![X16 : $i, X17 : $i]:
% 3.32/3.57         (((k2_xboole_0 @ (k1_tarski @ X17) @ X16) = (X16))
% 3.32/3.57          | ~ (r2_hidden @ X17 @ X16))),
% 3.32/3.57      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 3.32/3.57  thf('54', plain,
% 3.32/3.57      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_4))
% 3.32/3.57         = (k1_relat_1 @ sk_C_4))),
% 3.32/3.57      inference('sup-', [status(thm)], ['52', '53'])).
% 3.32/3.57  thf('55', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.32/3.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.32/3.57  thf('56', plain,
% 3.32/3.57      (((k2_xboole_0 @ (k1_relat_1 @ sk_C_4) @ (k1_tarski @ sk_A))
% 3.32/3.57         = (k1_relat_1 @ sk_C_4))),
% 3.32/3.57      inference('demod', [status(thm)], ['54', '55'])).
% 3.32/3.57  thf('57', plain,
% 3.32/3.57      (![X0 : $i, X1 : $i]:
% 3.32/3.57         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 3.32/3.57      inference('sup-', [status(thm)], ['23', '24'])).
% 3.32/3.57  thf('58', plain, (((k1_relat_1 @ sk_C_4) != (k1_xboole_0))),
% 3.32/3.57      inference('sup-', [status(thm)], ['56', '57'])).
% 3.32/3.57  thf('59', plain,
% 3.32/3.57      (![X0 : $i]:
% 3.32/3.57         (((k1_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.57          | ((sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_4)) = (sk_A)))),
% 3.32/3.57      inference('simplify_reflect-', [status(thm)], ['48', '58'])).
% 3.32/3.57  thf('60', plain,
% 3.32/3.57      (![X33 : $i, X34 : $i]:
% 3.32/3.57         (((X33) = (k1_xboole_0))
% 3.32/3.57          | ((sk_C_1 @ X34 @ X33) != (X34))
% 3.32/3.57          | ((X33) = (k1_tarski @ X34)))),
% 3.32/3.57      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 3.32/3.57  thf('61', plain,
% 3.32/3.57      (![X0 : $i]:
% 3.32/3.57         (((sk_A) != (X0))
% 3.32/3.57          | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.57          | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ X0))
% 3.32/3.57          | ((k1_relat_1 @ sk_C_4) = (k1_xboole_0)))),
% 3.32/3.57      inference('sup-', [status(thm)], ['59', '60'])).
% 3.32/3.57  thf('62', plain,
% 3.32/3.57      ((((k1_relat_1 @ sk_C_4) = (k1_xboole_0))
% 3.32/3.57        | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.32/3.57      inference('simplify', [status(thm)], ['61'])).
% 3.32/3.57  thf('63', plain, (((k1_relat_1 @ sk_C_4) != (k1_xboole_0))),
% 3.32/3.57      inference('sup-', [status(thm)], ['56', '57'])).
% 3.32/3.57  thf('64', plain, (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))),
% 3.32/3.57      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 3.32/3.57  thf('65', plain,
% 3.32/3.57      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A)))
% 3.32/3.57         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 3.32/3.57      inference('split', [status(esa)], ['31'])).
% 3.32/3.57  thf('66', plain,
% 3.32/3.57      ((((k1_relat_1 @ sk_C_4) != (k1_relat_1 @ sk_C_4)))
% 3.32/3.57         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 3.32/3.57      inference('sup-', [status(thm)], ['64', '65'])).
% 3.32/3.57  thf('67', plain, ((((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.32/3.57      inference('simplify', [status(thm)], ['66'])).
% 3.32/3.57  thf('68', plain,
% 3.32/3.57      (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))) | 
% 3.32/3.57       ~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.32/3.57      inference('split', [status(esa)], ['31'])).
% 3.32/3.57  thf('69', plain, (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 3.32/3.57      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 3.32/3.57  thf('70', plain, (((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B))),
% 3.32/3.57      inference('simpl_trail', [status(thm)], ['32', '69'])).
% 3.32/3.57  thf('71', plain, (((k2_relat_1 @ sk_C_4) != (k1_xboole_0))),
% 3.32/3.57      inference('sup-', [status(thm)], ['22', '25'])).
% 3.32/3.57  thf('72', plain, ($false),
% 3.32/3.57      inference('simplify_reflect-', [status(thm)], ['30', '70', '71'])).
% 3.32/3.57  
% 3.32/3.57  % SZS output end Refutation
% 3.32/3.57  
% 3.32/3.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
