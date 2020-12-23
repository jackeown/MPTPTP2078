%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRZjTcxU3d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:21 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 438 expanded)
%              Number of leaves         :   38 ( 149 expanded)
%              Depth                    :   24
%              Number of atoms          :  751 (3364 expanded)
%              Number of equality atoms :  102 ( 479 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_6_type,type,(
    sk_D_6: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ~ ( r2_hidden @ X81 @ X80 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_6 @ X81 @ X79 ) @ X81 ) @ X79 )
      | ( X80
       != ( k2_relat_1 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X79: $i,X81: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_6 @ X81 @ X79 ) @ X81 ) @ X79 )
      | ~ ( r2_hidden @ X81 @ ( k2_relat_1 @ X79 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_6 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_B @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X66 @ X67 ) )
      = ( k3_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X10 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X68: $i,X69: $i] :
      ( ( X68 = k1_xboole_0 )
      | ~ ( r1_tarski @ X69 @ ( sk_C_3 @ X69 @ X68 ) )
      | ( r1_tarski @ X69 @ ( k1_setfam_1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_3 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('15',plain,(
    ! [X62: $i,X63: $i] :
      ( ( X63 != X62 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X63 ) @ ( k1_tarski @ X62 ) )
       != ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('16',plain,(
    ! [X62: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X62 ) @ ( k1_tarski @ X62 ) )
     != ( k1_tarski @ X62 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X62: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X62 ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X68: $i,X69: $i] :
      ( ( X68 = k1_xboole_0 )
      | ~ ( r1_tarski @ X69 @ ( sk_C_3 @ X69 @ X68 ) )
      | ( r1_tarski @ X69 @ ( k1_setfam_1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X62: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X62 ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ( X47
       != ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X16: $i] :
      ( ( X16
        = ( k1_tarski @ X12 ) )
      | ( ( sk_C @ X16 @ X12 )
        = X12 )
      | ( r2_hidden @ ( sk_C @ X16 @ X12 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('36',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ X50 )
      | ( r2_hidden @ X52 @ X53 )
      | ( X53
       != ( k3_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('37',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X52 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X52 @ X50 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('40',plain,(
    ! [X65: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X62: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X62 ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 )
      | ( ( sk_C @ k1_xboole_0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X12: $i,X16: $i] :
      ( ( X16
        = ( k1_tarski @ X12 ) )
      | ( ( sk_C @ X16 @ X12 )
       != X12 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X12 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X62: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X62 ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','54'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('56',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( $false
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('61',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ~ ( r2_hidden @ X74 @ X73 )
      | ( r2_hidden @ ( k4_tarski @ X74 @ ( sk_D_4 @ X74 @ X72 ) ) @ X72 )
      | ( X73
       != ( k1_relat_1 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('62',plain,(
    ! [X72: $i,X74: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X74 @ ( sk_D_4 @ X74 @ X72 ) ) @ X72 )
      | ~ ( r2_hidden @ X74 @ ( k1_relat_1 @ X72 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_4 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('70',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['59','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRZjTcxU3d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.44/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.62  % Solved by: fo/fo7.sh
% 1.44/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.62  % done 1407 iterations in 1.150s
% 1.44/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.62  % SZS output start Refutation
% 1.44/1.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.44/1.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.44/1.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.44/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.62  thf(sk_B_type, type, sk_B: $i > $i).
% 1.44/1.62  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 1.44/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.44/1.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.44/1.62  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 1.44/1.62  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 1.44/1.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.44/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.44/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.62  thf(sk_D_6_type, type, sk_D_6: $i > $i > $i).
% 1.44/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.44/1.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.44/1.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.44/1.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.44/1.62  thf(t7_xboole_0, axiom,
% 1.44/1.62    (![A:$i]:
% 1.44/1.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.44/1.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.44/1.62  thf('0', plain,
% 1.44/1.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.44/1.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.44/1.62  thf(d5_relat_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.44/1.62       ( ![C:$i]:
% 1.44/1.62         ( ( r2_hidden @ C @ B ) <=>
% 1.44/1.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.44/1.62  thf('1', plain,
% 1.44/1.62      (![X79 : $i, X80 : $i, X81 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X81 @ X80)
% 1.44/1.62          | (r2_hidden @ (k4_tarski @ (sk_D_6 @ X81 @ X79) @ X81) @ X79)
% 1.44/1.62          | ((X80) != (k2_relat_1 @ X79)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.44/1.62  thf('2', plain,
% 1.44/1.62      (![X79 : $i, X81 : $i]:
% 1.44/1.62         ((r2_hidden @ (k4_tarski @ (sk_D_6 @ X81 @ X79) @ X81) @ X79)
% 1.44/1.62          | ~ (r2_hidden @ X81 @ (k2_relat_1 @ X79)))),
% 1.44/1.62      inference('simplify', [status(thm)], ['1'])).
% 1.44/1.62  thf('3', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.44/1.62          | (r2_hidden @ 
% 1.44/1.62             (k4_tarski @ (sk_D_6 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.44/1.62              (sk_B @ (k2_relat_1 @ X0))) @ 
% 1.44/1.62             X0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['0', '2'])).
% 1.44/1.62  thf(t69_enumset1, axiom,
% 1.44/1.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.44/1.62  thf('4', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 1.44/1.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.44/1.62  thf(t12_setfam_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.44/1.62  thf('5', plain,
% 1.44/1.62      (![X66 : $i, X67 : $i]:
% 1.44/1.62         ((k1_setfam_1 @ (k2_tarski @ X66 @ X67)) = (k3_xboole_0 @ X66 @ X67))),
% 1.44/1.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.44/1.62  thf('6', plain,
% 1.44/1.62      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 1.44/1.62      inference('sup+', [status(thm)], ['4', '5'])).
% 1.44/1.62  thf(idempotence_k3_xboole_0, axiom,
% 1.44/1.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.44/1.62  thf('7', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.44/1.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.44/1.62  thf('8', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 1.44/1.62      inference('demod', [status(thm)], ['6', '7'])).
% 1.44/1.62  thf(t61_xboole_1, axiom,
% 1.44/1.62    (![A:$i]:
% 1.44/1.62     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 1.44/1.62  thf('9', plain,
% 1.44/1.62      (![X10 : $i]:
% 1.44/1.62         ((r2_xboole_0 @ k1_xboole_0 @ X10) | ((X10) = (k1_xboole_0)))),
% 1.44/1.62      inference('cnf', [status(esa)], [t61_xboole_1])).
% 1.44/1.62  thf(d8_xboole_0, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 1.44/1.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 1.44/1.62  thf('10', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 1.44/1.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.44/1.62  thf('11', plain,
% 1.44/1.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['9', '10'])).
% 1.44/1.62  thf(t6_setfam_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 1.44/1.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 1.44/1.62  thf('12', plain,
% 1.44/1.62      (![X68 : $i, X69 : $i]:
% 1.44/1.62         (((X68) = (k1_xboole_0))
% 1.44/1.62          | ~ (r1_tarski @ X69 @ (sk_C_3 @ X69 @ X68))
% 1.44/1.62          | (r1_tarski @ X69 @ (k1_setfam_1 @ X68)))),
% 1.44/1.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.44/1.62  thf('13', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((sk_C_3 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 1.44/1.62          | (r1_tarski @ k1_xboole_0 @ (k1_setfam_1 @ X0))
% 1.44/1.62          | ((X0) = (k1_xboole_0)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['11', '12'])).
% 1.44/1.62  thf('14', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.44/1.62          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.44/1.62          | ((sk_C_3 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 1.44/1.62      inference('sup+', [status(thm)], ['8', '13'])).
% 1.44/1.62  thf(t20_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.44/1.62         ( k1_tarski @ A ) ) <=>
% 1.44/1.62       ( ( A ) != ( B ) ) ))).
% 1.44/1.62  thf('15', plain,
% 1.44/1.62      (![X62 : $i, X63 : $i]:
% 1.44/1.62         (((X63) != (X62))
% 1.44/1.62          | ((k4_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X62))
% 1.44/1.62              != (k1_tarski @ X63)))),
% 1.44/1.62      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.44/1.62  thf('16', plain,
% 1.44/1.62      (![X62 : $i]:
% 1.44/1.62         ((k4_xboole_0 @ (k1_tarski @ X62) @ (k1_tarski @ X62))
% 1.44/1.62           != (k1_tarski @ X62))),
% 1.44/1.62      inference('simplify', [status(thm)], ['15'])).
% 1.44/1.62  thf('17', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.44/1.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.44/1.62  thf(t100_xboole_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.44/1.62  thf('18', plain,
% 1.44/1.62      (![X8 : $i, X9 : $i]:
% 1.44/1.62         ((k4_xboole_0 @ X8 @ X9)
% 1.44/1.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.44/1.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.62  thf('19', plain,
% 1.44/1.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.44/1.62      inference('sup+', [status(thm)], ['17', '18'])).
% 1.44/1.62  thf(t92_xboole_1, axiom,
% 1.44/1.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.44/1.62  thf('20', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.44/1.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.44/1.62  thf('21', plain, (![X62 : $i]: ((k1_xboole_0) != (k1_tarski @ X62))),
% 1.44/1.62      inference('demod', [status(thm)], ['16', '19', '20'])).
% 1.44/1.62  thf('22', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((sk_C_3 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 1.44/1.62          | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.44/1.62      inference('clc', [status(thm)], ['14', '21'])).
% 1.44/1.62  thf('23', plain,
% 1.44/1.62      (![X68 : $i, X69 : $i]:
% 1.44/1.62         (((X68) = (k1_xboole_0))
% 1.44/1.62          | ~ (r1_tarski @ X69 @ (sk_C_3 @ X69 @ X68))
% 1.44/1.62          | (r1_tarski @ X69 @ (k1_setfam_1 @ X68)))),
% 1.44/1.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.44/1.62  thf('24', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 1.44/1.62          | (r1_tarski @ k1_xboole_0 @ X0)
% 1.44/1.62          | (r1_tarski @ k1_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 1.44/1.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['22', '23'])).
% 1.44/1.62  thf(d10_xboole_0, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.44/1.62  thf('25', plain,
% 1.44/1.62      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.62  thf('26', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 1.44/1.62      inference('simplify', [status(thm)], ['25'])).
% 1.44/1.62  thf('27', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 1.44/1.62      inference('demod', [status(thm)], ['6', '7'])).
% 1.44/1.62  thf('28', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.44/1.62          | (r1_tarski @ k1_xboole_0 @ X0)
% 1.44/1.62          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.44/1.62      inference('demod', [status(thm)], ['24', '26', '27'])).
% 1.44/1.62  thf('29', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((k1_tarski @ X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.44/1.62      inference('simplify', [status(thm)], ['28'])).
% 1.44/1.62  thf('30', plain, (![X62 : $i]: ((k1_xboole_0) != (k1_tarski @ X62))),
% 1.44/1.62      inference('demod', [status(thm)], ['16', '19', '20'])).
% 1.44/1.62  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.44/1.62      inference('clc', [status(thm)], ['29', '30'])).
% 1.44/1.62  thf(d1_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.44/1.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.44/1.62  thf('32', plain,
% 1.44/1.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.44/1.62         (~ (r1_tarski @ X45 @ X46)
% 1.44/1.62          | (r2_hidden @ X45 @ X47)
% 1.44/1.62          | ((X47) != (k1_zfmisc_1 @ X46)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.44/1.62  thf('33', plain,
% 1.44/1.62      (![X45 : $i, X46 : $i]:
% 1.44/1.62         ((r2_hidden @ X45 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X45 @ X46))),
% 1.44/1.62      inference('simplify', [status(thm)], ['32'])).
% 1.44/1.62  thf('34', plain,
% 1.44/1.62      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['31', '33'])).
% 1.44/1.62  thf(d1_tarski, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.44/1.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.44/1.62  thf('35', plain,
% 1.44/1.62      (![X12 : $i, X16 : $i]:
% 1.44/1.62         (((X16) = (k1_tarski @ X12))
% 1.44/1.62          | ((sk_C @ X16 @ X12) = (X12))
% 1.44/1.62          | (r2_hidden @ (sk_C @ X16 @ X12) @ X16))),
% 1.44/1.62      inference('cnf', [status(esa)], [d1_tarski])).
% 1.44/1.62  thf(d4_tarski, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.44/1.62       ( ![C:$i]:
% 1.44/1.62         ( ( r2_hidden @ C @ B ) <=>
% 1.44/1.62           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.44/1.62  thf('36', plain,
% 1.44/1.62      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X50 @ X51)
% 1.44/1.62          | ~ (r2_hidden @ X52 @ X50)
% 1.44/1.62          | (r2_hidden @ X52 @ X53)
% 1.44/1.62          | ((X53) != (k3_tarski @ X51)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d4_tarski])).
% 1.44/1.62  thf('37', plain,
% 1.44/1.62      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.44/1.62         ((r2_hidden @ X52 @ (k3_tarski @ X51))
% 1.44/1.62          | ~ (r2_hidden @ X52 @ X50)
% 1.44/1.62          | ~ (r2_hidden @ X50 @ X51))),
% 1.44/1.62      inference('simplify', [status(thm)], ['36'])).
% 1.44/1.62  thf('38', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.62         (((sk_C @ X0 @ X1) = (X1))
% 1.44/1.62          | ((X0) = (k1_tarski @ X1))
% 1.44/1.62          | ~ (r2_hidden @ X0 @ X2)
% 1.44/1.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_tarski @ X2)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['35', '37'])).
% 1.44/1.62  thf('39', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ 
% 1.44/1.62           (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 1.44/1.62          | ((k1_xboole_0) = (k1_tarski @ X1))
% 1.44/1.62          | ((sk_C @ k1_xboole_0 @ X1) = (X1)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['34', '38'])).
% 1.44/1.62  thf(t99_zfmisc_1, axiom,
% 1.44/1.62    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.44/1.62  thf('40', plain, (![X65 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X65)) = (X65))),
% 1.44/1.62      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.44/1.62  thf('41', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X0)
% 1.44/1.62          | ((k1_xboole_0) = (k1_tarski @ X1))
% 1.44/1.62          | ((sk_C @ k1_xboole_0 @ X1) = (X1)))),
% 1.44/1.62      inference('demod', [status(thm)], ['39', '40'])).
% 1.44/1.62  thf('42', plain, (![X62 : $i]: ((k1_xboole_0) != (k1_tarski @ X62))),
% 1.44/1.62      inference('demod', [status(thm)], ['16', '19', '20'])).
% 1.44/1.62  thf('43', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 1.44/1.62          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X0))),
% 1.44/1.62      inference('clc', [status(thm)], ['41', '42'])).
% 1.44/1.62  thf('44', plain,
% 1.44/1.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X15 @ X14)
% 1.44/1.62          | ((X15) = (X12))
% 1.44/1.62          | ((X14) != (k1_tarski @ X12)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d1_tarski])).
% 1.44/1.62  thf('45', plain,
% 1.44/1.62      (![X12 : $i, X15 : $i]:
% 1.44/1.62         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 1.44/1.62      inference('simplify', [status(thm)], ['44'])).
% 1.44/1.62  thf('46', plain,
% 1.44/1.62      (![X0 : $i, X1 : $i]:
% 1.44/1.62         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 1.44/1.62          | ((sk_C @ k1_xboole_0 @ X1) = (X0)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['43', '45'])).
% 1.44/1.62  thf('47', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.62      inference('condensation', [status(thm)], ['46'])).
% 1.44/1.62  thf('48', plain,
% 1.44/1.62      (![X12 : $i, X16 : $i]:
% 1.44/1.62         (((X16) = (k1_tarski @ X12))
% 1.44/1.62          | ((sk_C @ X16 @ X12) != (X12))
% 1.44/1.62          | ~ (r2_hidden @ (sk_C @ X16 @ X12) @ X16))),
% 1.44/1.62      inference('cnf', [status(esa)], [d1_tarski])).
% 1.44/1.62  thf('49', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.44/1.62          | ((sk_C @ k1_xboole_0 @ X0) != (X0))
% 1.44/1.62          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 1.44/1.62      inference('sup-', [status(thm)], ['47', '48'])).
% 1.44/1.62  thf('50', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.62      inference('condensation', [status(thm)], ['46'])).
% 1.44/1.62  thf('51', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.44/1.62          | ((X0) != (X0))
% 1.44/1.62          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 1.44/1.62      inference('demod', [status(thm)], ['49', '50'])).
% 1.44/1.62  thf('52', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 1.44/1.62      inference('simplify', [status(thm)], ['51'])).
% 1.44/1.62  thf('53', plain, (![X62 : $i]: ((k1_xboole_0) != (k1_tarski @ X62))),
% 1.44/1.62      inference('demod', [status(thm)], ['16', '19', '20'])).
% 1.44/1.62  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.44/1.62      inference('clc', [status(thm)], ['52', '53'])).
% 1.44/1.62  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['3', '54'])).
% 1.44/1.62  thf(t60_relat_1, conjecture,
% 1.44/1.62    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.44/1.62     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.44/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.62    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.44/1.62        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 1.44/1.62    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 1.44/1.62  thf('56', plain,
% 1.44/1.62      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 1.44/1.62        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 1.44/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.62  thf('57', plain,
% 1.44/1.62      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 1.44/1.62         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 1.44/1.62      inference('split', [status(esa)], ['56'])).
% 1.44/1.62  thf('58', plain,
% 1.44/1.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.44/1.62         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 1.44/1.62      inference('sup-', [status(thm)], ['55', '57'])).
% 1.44/1.62  thf('59', plain,
% 1.44/1.62      (($false) <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 1.44/1.62      inference('simplify', [status(thm)], ['58'])).
% 1.44/1.62  thf('60', plain,
% 1.44/1.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.44/1.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.44/1.62  thf(d4_relat_1, axiom,
% 1.44/1.62    (![A:$i,B:$i]:
% 1.44/1.62     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.44/1.62       ( ![C:$i]:
% 1.44/1.62         ( ( r2_hidden @ C @ B ) <=>
% 1.44/1.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.44/1.62  thf('61', plain,
% 1.44/1.62      (![X72 : $i, X73 : $i, X74 : $i]:
% 1.44/1.62         (~ (r2_hidden @ X74 @ X73)
% 1.44/1.62          | (r2_hidden @ (k4_tarski @ X74 @ (sk_D_4 @ X74 @ X72)) @ X72)
% 1.44/1.62          | ((X73) != (k1_relat_1 @ X72)))),
% 1.44/1.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.44/1.62  thf('62', plain,
% 1.44/1.62      (![X72 : $i, X74 : $i]:
% 1.44/1.62         ((r2_hidden @ (k4_tarski @ X74 @ (sk_D_4 @ X74 @ X72)) @ X72)
% 1.44/1.62          | ~ (r2_hidden @ X74 @ (k1_relat_1 @ X72)))),
% 1.44/1.62      inference('simplify', [status(thm)], ['61'])).
% 1.44/1.62  thf('63', plain,
% 1.44/1.62      (![X0 : $i]:
% 1.44/1.62         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 1.44/1.62          | (r2_hidden @ 
% 1.44/1.62             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 1.44/1.62              (sk_D_4 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 1.44/1.62             X0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['60', '62'])).
% 1.44/1.62  thf('64', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.44/1.62      inference('clc', [status(thm)], ['52', '53'])).
% 1.44/1.62  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.44/1.62      inference('sup-', [status(thm)], ['63', '64'])).
% 1.44/1.62  thf('66', plain,
% 1.44/1.62      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 1.44/1.62         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 1.44/1.62      inference('split', [status(esa)], ['56'])).
% 1.44/1.62  thf('67', plain,
% 1.44/1.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.44/1.62         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 1.44/1.62      inference('sup-', [status(thm)], ['65', '66'])).
% 1.44/1.62  thf('68', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.44/1.62      inference('simplify', [status(thm)], ['67'])).
% 1.44/1.62  thf('69', plain,
% 1.44/1.62      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.44/1.62       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.44/1.62      inference('split', [status(esa)], ['56'])).
% 1.44/1.62  thf('70', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.44/1.62      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 1.44/1.62  thf('71', plain, ($false),
% 1.44/1.62      inference('simpl_trail', [status(thm)], ['59', '70'])).
% 1.44/1.62  
% 1.44/1.62  % SZS output end Refutation
% 1.44/1.62  
% 1.44/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
