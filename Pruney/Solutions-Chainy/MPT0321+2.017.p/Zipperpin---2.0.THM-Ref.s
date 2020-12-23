%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XTsKBvoz08

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:35 EST 2020

% Result     : Theorem 6.32s
% Output     : Refutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  142 (2134 expanded)
%              Number of leaves         :   19 ( 695 expanded)
%              Depth                    :   26
%              Number of atoms          : 1168 (23663 expanded)
%              Number of equality atoms :  118 (2595 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X50 @ X52 ) @ X51 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( k2_zfmisc_1 @ X53 @ ( k3_xboole_0 @ X50 @ X52 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X50 ) @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('4',plain,
    ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r1_tarski @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X48 @ X47 ) @ ( k2_zfmisc_1 @ X49 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X50 @ X52 ) @ X51 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('15',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( k2_zfmisc_1 @ X53 @ ( k3_xboole_0 @ X50 @ X52 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X50 ) @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('17',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( k2_zfmisc_1 @ X53 @ ( k3_xboole_0 @ X50 @ X52 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X50 ) @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      = ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','21'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_C_3 ) @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('39',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X50 @ X52 ) @ X51 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['23','36','37','38','39','40','43','44'])).

thf('46',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['12','45','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('61',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X50 @ X52 ) @ X51 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('65',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( k2_zfmisc_1 @ X53 @ ( k3_xboole_0 @ X50 @ X52 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X50 ) @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_D_2 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('72',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','72','73'])).

thf('75',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r1_tarski @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X48 @ X47 ) @ ( k2_zfmisc_1 @ X49 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','72','73'])).

thf('80',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r1_tarski @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
      | ( r1_tarski @ X0 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
    | ( r1_tarski @ sk_D_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('89',plain,(
    r1_tarski @ sk_D_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('91',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ sk_B_1 )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('93',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r1_tarski @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
    | ( r1_tarski @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('100',plain,(
    r1_tarski @ sk_B_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    sk_D_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['91','104'])).

thf('106',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','105','106'])).

thf('108',plain,(
    r1_tarski @ sk_C_3 @ sk_A ),
    inference('sup-',[status(thm)],['58','107'])).

thf('109',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_C_3 ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_A = sk_C_3 ),
    inference('sup+',[status(thm)],['57','110'])).

thf('112',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B_1 != sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,(
    sk_D_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['91','104'])).

thf('115',plain,
    ( ( sk_B_1 != sk_D_2 )
   <= ( sk_B_1 != sk_D_2 ) ),
    inference(split,[status(esa)],['112'])).

thf('116',plain,
    ( ( sk_D_2 != sk_D_2 )
   <= ( sk_B_1 != sk_D_2 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_B_1 = sk_D_2 ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B_1 != sk_D_2 ) ),
    inference(split,[status(esa)],['112'])).

thf('119',plain,(
    sk_A != sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_A != sk_C_3 ),
    inference(simpl_trail,[status(thm)],['113','119'])).

thf('121',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XTsKBvoz08
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 6.32/6.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.32/6.59  % Solved by: fo/fo7.sh
% 6.32/6.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.32/6.59  % done 6576 iterations in 6.113s
% 6.32/6.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.32/6.59  % SZS output start Refutation
% 6.32/6.59  thf(sk_A_type, type, sk_A: $i).
% 6.32/6.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.32/6.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.32/6.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.32/6.59  thf(sk_C_3_type, type, sk_C_3: $i).
% 6.32/6.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.32/6.59  thf(sk_D_2_type, type, sk_D_2: $i).
% 6.32/6.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.32/6.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.32/6.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.32/6.59  thf(t134_zfmisc_1, conjecture,
% 6.32/6.59    (![A:$i,B:$i,C:$i,D:$i]:
% 6.32/6.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 6.32/6.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.32/6.59         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 6.32/6.59  thf(zf_stmt_0, negated_conjecture,
% 6.32/6.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.32/6.59        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 6.32/6.59          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.32/6.59            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 6.32/6.59    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 6.32/6.59  thf('0', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf(t122_zfmisc_1, axiom,
% 6.32/6.59    (![A:$i,B:$i,C:$i]:
% 6.32/6.59     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 6.32/6.59         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 6.32/6.59       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 6.32/6.59         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 6.32/6.59  thf('1', plain,
% 6.32/6.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X50 @ X52) @ X51)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X52 @ X51)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('2', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['0', '1'])).
% 6.32/6.59  thf('3', plain,
% 6.32/6.59      (![X50 : $i, X52 : $i, X53 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ X53 @ (k3_xboole_0 @ X50 @ X52))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X50) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X53 @ X52)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('4', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_3) @ sk_B_1))),
% 6.32/6.59      inference('sup+', [status(thm)], ['2', '3'])).
% 6.32/6.59  thf(commutativity_k3_xboole_0, axiom,
% 6.32/6.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.32/6.59  thf('5', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('6', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_B_1))),
% 6.32/6.59      inference('demod', [status(thm)], ['4', '5'])).
% 6.32/6.59  thf('7', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf(t117_zfmisc_1, axiom,
% 6.32/6.59    (![A:$i,B:$i,C:$i]:
% 6.32/6.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 6.32/6.59          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 6.32/6.59            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 6.32/6.59          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 6.32/6.59  thf('8', plain,
% 6.32/6.59      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.32/6.59         (((X47) = (k1_xboole_0))
% 6.32/6.59          | (r1_tarski @ X48 @ X49)
% 6.32/6.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X48 @ X47) @ 
% 6.32/6.59               (k2_zfmisc_1 @ X49 @ X47)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 6.32/6.59  thf('9', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 6.32/6.59          | (r1_tarski @ sk_A @ X0)
% 6.32/6.59          | ((sk_B_1) = (k1_xboole_0)))),
% 6.32/6.59      inference('sup-', [status(thm)], ['7', '8'])).
% 6.32/6.59  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('11', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 6.32/6.59          | (r1_tarski @ sk_A @ X0))),
% 6.32/6.59      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 6.32/6.59  thf('12', plain,
% 6.32/6.59      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59           (k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1)))
% 6.32/6.59        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_3 @ sk_A)))),
% 6.32/6.59      inference('sup-', [status(thm)], ['6', '11'])).
% 6.32/6.59  thf('13', plain,
% 6.32/6.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X50 @ X52) @ X51)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X52 @ X51)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('14', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_B_1))),
% 6.32/6.59      inference('demod', [status(thm)], ['4', '5'])).
% 6.32/6.59  thf('15', plain,
% 6.32/6.59      (![X50 : $i, X52 : $i, X53 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ X53 @ (k3_xboole_0 @ X50 @ X52))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X50) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X53 @ X52)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('16', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ 
% 6.32/6.59           (k3_xboole_0 @ X0 @ sk_B_1))
% 6.32/6.59           = (k3_xboole_0 @ 
% 6.32/6.59              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ X0) @ 
% 6.32/6.59              (k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))))),
% 6.32/6.59      inference('sup+', [status(thm)], ['14', '15'])).
% 6.32/6.59  thf(t123_zfmisc_1, axiom,
% 6.32/6.59    (![A:$i,B:$i,C:$i,D:$i]:
% 6.32/6.59     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 6.32/6.59       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 6.32/6.59  thf('17', plain,
% 6.32/6.59      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X56 @ X57)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 6.32/6.59  thf('18', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('19', plain,
% 6.32/6.59      (![X50 : $i, X52 : $i, X53 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ X53 @ (k3_xboole_0 @ X50 @ X52))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X50) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X53 @ X52)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('20', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('21', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X2 @ X1))
% 6.32/6.59           = (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['19', '20'])).
% 6.32/6.59  thf('22', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ X0))
% 6.32/6.59           = (k3_xboole_0 @ 
% 6.32/6.59              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ X0) @ 
% 6.32/6.59              (k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))))),
% 6.32/6.59      inference('demod', [status(thm)], ['16', '17', '18', '21'])).
% 6.32/6.59  thf('23', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_C_3 @ 
% 6.32/6.59         (k3_xboole_0 @ sk_D_2 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1)))
% 6.32/6.59         = (k2_zfmisc_1 @ 
% 6.32/6.59            (k3_xboole_0 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_C_3) @ 
% 6.32/6.59            (k3_xboole_0 @ sk_D_2 @ sk_B_1)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['13', '22'])).
% 6.32/6.59  thf('24', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf(d3_tarski, axiom,
% 6.32/6.59    (![A:$i,B:$i]:
% 6.32/6.59     ( ( r1_tarski @ A @ B ) <=>
% 6.32/6.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.32/6.59  thf('25', plain,
% 6.32/6.59      (![X6 : $i, X8 : $i]:
% 6.32/6.59         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 6.32/6.59      inference('cnf', [status(esa)], [d3_tarski])).
% 6.32/6.59  thf(d4_xboole_0, axiom,
% 6.32/6.59    (![A:$i,B:$i,C:$i]:
% 6.32/6.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 6.32/6.59       ( ![D:$i]:
% 6.32/6.59         ( ( r2_hidden @ D @ C ) <=>
% 6.32/6.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.32/6.59  thf('26', plain,
% 6.32/6.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.32/6.59         (~ (r2_hidden @ X13 @ X12)
% 6.32/6.59          | (r2_hidden @ X13 @ X11)
% 6.32/6.59          | ((X12) != (k3_xboole_0 @ X10 @ X11)))),
% 6.32/6.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.32/6.59  thf('27', plain,
% 6.32/6.59      (![X10 : $i, X11 : $i, X13 : $i]:
% 6.32/6.59         ((r2_hidden @ X13 @ X11)
% 6.32/6.59          | ~ (r2_hidden @ X13 @ (k3_xboole_0 @ X10 @ X11)))),
% 6.32/6.59      inference('simplify', [status(thm)], ['26'])).
% 6.32/6.59  thf('28', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.59         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 6.32/6.59          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 6.32/6.59      inference('sup-', [status(thm)], ['25', '27'])).
% 6.32/6.59  thf('29', plain,
% 6.32/6.59      (![X6 : $i, X8 : $i]:
% 6.32/6.59         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 6.32/6.59      inference('cnf', [status(esa)], [d3_tarski])).
% 6.32/6.59  thf('30', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 6.32/6.59          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 6.32/6.59      inference('sup-', [status(thm)], ['28', '29'])).
% 6.32/6.59  thf('31', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.32/6.59      inference('simplify', [status(thm)], ['30'])).
% 6.32/6.59  thf('32', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.32/6.59      inference('sup+', [status(thm)], ['24', '31'])).
% 6.32/6.59  thf(t28_xboole_1, axiom,
% 6.32/6.59    (![A:$i,B:$i]:
% 6.32/6.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.32/6.59  thf('33', plain,
% 6.32/6.59      (![X27 : $i, X28 : $i]:
% 6.32/6.59         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 6.32/6.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.32/6.59  thf('34', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 6.32/6.59           = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('sup-', [status(thm)], ['32', '33'])).
% 6.32/6.59  thf('35', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('36', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.32/6.59           = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('demod', [status(thm)], ['34', '35'])).
% 6.32/6.59  thf('37', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('38', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.32/6.59           = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('demod', [status(thm)], ['34', '35'])).
% 6.32/6.59  thf('39', plain,
% 6.32/6.59      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X56 @ X57)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 6.32/6.59  thf('40', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('41', plain,
% 6.32/6.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X50 @ X52) @ X51)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X52 @ X51)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('42', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('43', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X2 @ X0))
% 6.32/6.59           = (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 6.32/6.59      inference('sup+', [status(thm)], ['41', '42'])).
% 6.32/6.59  thf(idempotence_k3_xboole_0, axiom,
% 6.32/6.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 6.32/6.59  thf('44', plain, (![X18 : $i]: ((k3_xboole_0 @ X18 @ X18) = (X18))),
% 6.32/6.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 6.32/6.59  thf('45', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('demod', [status(thm)],
% 6.32/6.59                ['23', '36', '37', '38', '39', '40', '43', '44'])).
% 6.32/6.59  thf('46', plain,
% 6.32/6.59      (![X6 : $i, X8 : $i]:
% 6.32/6.59         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 6.32/6.59      inference('cnf', [status(esa)], [d3_tarski])).
% 6.32/6.59  thf('47', plain,
% 6.32/6.59      (![X6 : $i, X8 : $i]:
% 6.32/6.59         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 6.32/6.59      inference('cnf', [status(esa)], [d3_tarski])).
% 6.32/6.59  thf('48', plain,
% 6.32/6.59      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 6.32/6.59      inference('sup-', [status(thm)], ['46', '47'])).
% 6.32/6.59  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.32/6.59      inference('simplify', [status(thm)], ['48'])).
% 6.32/6.59  thf('50', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_3 @ sk_A))),
% 6.32/6.59      inference('demod', [status(thm)], ['12', '45', '49'])).
% 6.32/6.59  thf('51', plain,
% 6.32/6.59      (![X27 : $i, X28 : $i]:
% 6.32/6.59         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 6.32/6.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.32/6.59  thf('52', plain,
% 6.32/6.59      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_3 @ sk_A)) = (sk_A))),
% 6.32/6.59      inference('sup-', [status(thm)], ['50', '51'])).
% 6.32/6.59  thf('53', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('54', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.32/6.59           = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('demod', [status(thm)], ['34', '35'])).
% 6.32/6.59  thf('55', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 6.32/6.59           = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('sup+', [status(thm)], ['53', '54'])).
% 6.32/6.59  thf('56', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('57', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 6.32/6.59      inference('demod', [status(thm)], ['52', '55', '56'])).
% 6.32/6.59  thf('58', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.32/6.59      inference('simplify', [status(thm)], ['48'])).
% 6.32/6.59  thf('59', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['0', '1'])).
% 6.32/6.59  thf('60', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 6.32/6.59      inference('demod', [status(thm)], ['52', '55', '56'])).
% 6.32/6.59  thf('61', plain,
% 6.32/6.59      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X56 @ X57)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 6.32/6.59  thf('62', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ X1) @ 
% 6.32/6.59              (k2_zfmisc_1 @ sk_A @ X0)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['60', '61'])).
% 6.32/6.59  thf('63', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B_1))),
% 6.32/6.59      inference('sup+', [status(thm)], ['59', '62'])).
% 6.32/6.59  thf('64', plain,
% 6.32/6.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ (k3_xboole_0 @ X50 @ X52) @ X51)
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X52 @ X51)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('65', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('66', plain,
% 6.32/6.59      (![X50 : $i, X52 : $i, X53 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ X53 @ (k3_xboole_0 @ X50 @ X52))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X50) @ 
% 6.32/6.59              (k2_zfmisc_1 @ X53 @ X52)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 6.32/6.59  thf('67', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0))
% 6.32/6.59           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59              (k2_zfmisc_1 @ sk_A @ X0)))),
% 6.32/6.59      inference('sup+', [status(thm)], ['65', '66'])).
% 6.32/6.59  thf('68', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_D_2))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2))),
% 6.32/6.59      inference('sup+', [status(thm)], ['64', '67'])).
% 6.32/6.59  thf('69', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('70', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2))),
% 6.32/6.59      inference('demod', [status(thm)], ['68', '69'])).
% 6.32/6.59  thf('71', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 6.32/6.59      inference('demod', [status(thm)], ['52', '55', '56'])).
% 6.32/6.59  thf('72', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B_1))
% 6.32/6.59         = (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 6.32/6.59      inference('demod', [status(thm)], ['70', '71'])).
% 6.32/6.59  thf('73', plain, (![X18 : $i]: ((k3_xboole_0 @ X18 @ X18) = (X18))),
% 6.32/6.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 6.32/6.59  thf('74', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.32/6.59      inference('demod', [status(thm)], ['63', '72', '73'])).
% 6.32/6.59  thf('75', plain,
% 6.32/6.59      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.32/6.59         (((X47) = (k1_xboole_0))
% 6.32/6.59          | (r1_tarski @ X48 @ X49)
% 6.32/6.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X48 @ X47) @ 
% 6.32/6.59               (k2_zfmisc_1 @ X49 @ X47)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 6.32/6.59  thf('76', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_A @ sk_D_2))
% 6.32/6.59          | (r1_tarski @ X0 @ sk_A)
% 6.32/6.59          | ((sk_B_1) = (k1_xboole_0)))),
% 6.32/6.59      inference('sup-', [status(thm)], ['74', '75'])).
% 6.32/6.59  thf('77', plain, (((sk_B_1) != (k1_xboole_0))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('78', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_A @ sk_D_2))
% 6.32/6.59          | (r1_tarski @ X0 @ sk_A))),
% 6.32/6.59      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 6.32/6.59  thf('79', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 6.32/6.59      inference('demod', [status(thm)], ['63', '72', '73'])).
% 6.32/6.59  thf('80', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('81', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('sup+', [status(thm)], ['79', '80'])).
% 6.32/6.59  thf('82', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('83', plain,
% 6.32/6.59      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.32/6.59         (((X47) = (k1_xboole_0))
% 6.32/6.59          | (r1_tarski @ X48 @ X49)
% 6.32/6.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 6.32/6.59               (k2_zfmisc_1 @ X47 @ X49)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 6.32/6.59  thf('84', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 6.32/6.59          | (r1_tarski @ X0 @ sk_B_1)
% 6.32/6.59          | ((sk_A) = (k1_xboole_0)))),
% 6.32/6.59      inference('sup-', [status(thm)], ['82', '83'])).
% 6.32/6.59  thf('85', plain, (((sk_A) != (k1_xboole_0))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('86', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 6.32/6.59          | (r1_tarski @ X0 @ sk_B_1))),
% 6.32/6.59      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 6.32/6.59  thf('87', plain,
% 6.32/6.59      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59           (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 6.32/6.59        | (r1_tarski @ sk_D_2 @ sk_B_1))),
% 6.32/6.59      inference('sup-', [status(thm)], ['81', '86'])).
% 6.32/6.59  thf('88', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.32/6.59      inference('simplify', [status(thm)], ['48'])).
% 6.32/6.59  thf('89', plain, ((r1_tarski @ sk_D_2 @ sk_B_1)),
% 6.32/6.59      inference('demod', [status(thm)], ['87', '88'])).
% 6.32/6.59  thf('90', plain,
% 6.32/6.59      (![X27 : $i, X28 : $i]:
% 6.32/6.59         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 6.32/6.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.32/6.59  thf('91', plain, (((k3_xboole_0 @ sk_D_2 @ sk_B_1) = (sk_D_2))),
% 6.32/6.59      inference('sup-', [status(thm)], ['89', '90'])).
% 6.32/6.59  thf('92', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('sup+', [status(thm)], ['79', '80'])).
% 6.32/6.59  thf('93', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('94', plain,
% 6.32/6.59      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.32/6.59         (((X47) = (k1_xboole_0))
% 6.32/6.59          | (r1_tarski @ X48 @ X49)
% 6.32/6.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 6.32/6.59               (k2_zfmisc_1 @ X47 @ X49)))),
% 6.32/6.59      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 6.32/6.59  thf('95', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_A @ X0))
% 6.32/6.59          | (r1_tarski @ sk_B_1 @ X0)
% 6.32/6.59          | ((sk_A) = (k1_xboole_0)))),
% 6.32/6.59      inference('sup-', [status(thm)], ['93', '94'])).
% 6.32/6.59  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('97', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_A @ X0))
% 6.32/6.59          | (r1_tarski @ sk_B_1 @ X0))),
% 6.32/6.59      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 6.32/6.59  thf('98', plain,
% 6.32/6.59      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 6.32/6.59           (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 6.32/6.59        | (r1_tarski @ sk_B_1 @ sk_D_2))),
% 6.32/6.59      inference('sup-', [status(thm)], ['92', '97'])).
% 6.32/6.59  thf('99', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.32/6.59      inference('simplify', [status(thm)], ['48'])).
% 6.32/6.59  thf('100', plain, ((r1_tarski @ sk_B_1 @ sk_D_2)),
% 6.32/6.59      inference('demod', [status(thm)], ['98', '99'])).
% 6.32/6.59  thf('101', plain,
% 6.32/6.59      (![X27 : $i, X28 : $i]:
% 6.32/6.59         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 6.32/6.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.32/6.59  thf('102', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D_2) = (sk_B_1))),
% 6.32/6.59      inference('sup-', [status(thm)], ['100', '101'])).
% 6.32/6.59  thf('103', plain,
% 6.32/6.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.32/6.59  thf('104', plain, (((k3_xboole_0 @ sk_D_2 @ sk_B_1) = (sk_B_1))),
% 6.32/6.59      inference('demod', [status(thm)], ['102', '103'])).
% 6.32/6.59  thf('105', plain, (((sk_D_2) = (sk_B_1))),
% 6.32/6.59      inference('sup+', [status(thm)], ['91', '104'])).
% 6.32/6.59  thf('106', plain,
% 6.32/6.59      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 6.32/6.59      inference('sup+', [status(thm)], ['79', '80'])).
% 6.32/6.59  thf('107', plain,
% 6.32/6.59      (![X0 : $i]:
% 6.32/6.59         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D_2) @ 
% 6.32/6.59             (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 6.32/6.59          | (r1_tarski @ X0 @ sk_A))),
% 6.32/6.59      inference('demod', [status(thm)], ['78', '105', '106'])).
% 6.32/6.59  thf('108', plain, ((r1_tarski @ sk_C_3 @ sk_A)),
% 6.32/6.59      inference('sup-', [status(thm)], ['58', '107'])).
% 6.32/6.59  thf('109', plain,
% 6.32/6.59      (![X27 : $i, X28 : $i]:
% 6.32/6.59         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 6.32/6.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.32/6.59  thf('110', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_C_3))),
% 6.32/6.59      inference('sup-', [status(thm)], ['108', '109'])).
% 6.32/6.59  thf('111', plain, (((sk_A) = (sk_C_3))),
% 6.32/6.59      inference('sup+', [status(thm)], ['57', '110'])).
% 6.32/6.59  thf('112', plain, ((((sk_A) != (sk_C_3)) | ((sk_B_1) != (sk_D_2)))),
% 6.32/6.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.59  thf('113', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 6.32/6.59      inference('split', [status(esa)], ['112'])).
% 6.32/6.59  thf('114', plain, (((sk_D_2) = (sk_B_1))),
% 6.32/6.59      inference('sup+', [status(thm)], ['91', '104'])).
% 6.32/6.59  thf('115', plain, ((((sk_B_1) != (sk_D_2))) <= (~ (((sk_B_1) = (sk_D_2))))),
% 6.32/6.59      inference('split', [status(esa)], ['112'])).
% 6.32/6.59  thf('116', plain, ((((sk_D_2) != (sk_D_2))) <= (~ (((sk_B_1) = (sk_D_2))))),
% 6.32/6.59      inference('sup-', [status(thm)], ['114', '115'])).
% 6.32/6.59  thf('117', plain, ((((sk_B_1) = (sk_D_2)))),
% 6.32/6.59      inference('simplify', [status(thm)], ['116'])).
% 6.32/6.59  thf('118', plain, (~ (((sk_A) = (sk_C_3))) | ~ (((sk_B_1) = (sk_D_2)))),
% 6.32/6.59      inference('split', [status(esa)], ['112'])).
% 6.32/6.59  thf('119', plain, (~ (((sk_A) = (sk_C_3)))),
% 6.32/6.59      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 6.32/6.59  thf('120', plain, (((sk_A) != (sk_C_3))),
% 6.32/6.59      inference('simpl_trail', [status(thm)], ['113', '119'])).
% 6.32/6.59  thf('121', plain, ($false),
% 6.32/6.59      inference('simplify_reflect-', [status(thm)], ['111', '120'])).
% 6.32/6.59  
% 6.32/6.59  % SZS output end Refutation
% 6.32/6.59  
% 6.32/6.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
