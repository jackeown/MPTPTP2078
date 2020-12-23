%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRONSXHZBA

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  144 (2766 expanded)
%              Number of leaves         :   16 ( 824 expanded)
%              Depth                    :   28
%              Number of atoms          : 1280 (40807 expanded)
%              Number of equality atoms :  159 (7687 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t36_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_mcart_1])).

thf('3',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r1_tarski @ X0 @ X3 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r1_tarski @ X0 @ X3 )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('17',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    r1_tarski @ sk_C @ sk_F ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_F @ sk_C )
    | ( sk_F = sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('29',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X3 @ X0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('39',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['26','39'])).

thf('41',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X4 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X4 @ X3 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X4 )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('55',plain,
    ( ( r1_tarski @ sk_A @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ sk_A @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_A )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('65',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('70',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','40'])).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('80',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('84',plain,
    ( ( r1_tarski @ sk_B @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_E ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ sk_B @ sk_E ),
    inference('simplify_reflect-',[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_B )
    | ( sk_E = sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('94',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','80'])).

thf('95',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','80'])).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ( k2_zfmisc_1 @ sk_D @ sk_E )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['100','101','102'])).

thf('104',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['97','103'])).

thf('105',plain,(
    sk_E = sk_B ),
    inference(demod,[status(thm)],['92','104'])).

thf('106',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = ( k2_zfmisc_1 @ sk_A @ sk_E ) ),
    inference(demod,[status(thm)],['81','105'])).

thf('107',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      | ( r1_tarski @ X1 @ sk_A )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['64','108'])).

thf('110',plain,(
    ( k2_zfmisc_1 @ sk_D @ sk_E )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['100','101','102'])).

thf('111',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_D = sk_A ),
    inference(demod,[status(thm)],['63','111'])).

thf('113',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['26','39'])).

thf('116',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('117',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    sk_E = sk_B ),
    inference(demod,[status(thm)],['92','104'])).

thf('120',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['113'])).

thf('121',plain,
    ( ( sk_E != sk_E )
   <= ( sk_B != sk_E ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_B = sk_E ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('124',plain,(
    sk_A != sk_D ),
    inference('sat_resolution*',[status(thm)],['118','122','123'])).

thf('125',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['114','124'])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRONSXHZBA
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 253 iterations in 0.120s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf(d3_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.58       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf(t36_mcart_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.58     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.58        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.58          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58            ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t36_mcart_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf(t138_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.58       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X7 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.20/0.58          | (r1_tarski @ X0 @ X3)
% 0.20/0.58          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.20/0.58          | (r1_tarski @ X0 @ X3)
% 0.20/0.58          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ sk_C @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | ((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ sk_C @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t35_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.58       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.58         (((k3_zfmisc_1 @ X13 @ X14 @ X15) != (k1_xboole_0))
% 0.20/0.58          | ((X15) = (k1_xboole_0))
% 0.20/0.58          | ((X14) = (k1_xboole_0))
% 0.20/0.58          | ((X13) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('21', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ sk_C @ X0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['14', '21'])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ sk_C @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '22'])).
% 0.20/0.58  thf('24', plain, ((r1_tarski @ sk_C @ sk_F)),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('26', plain, ((~ (r1_tarski @ sk_F @ sk_C) | ((sk_F) = (sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.58  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X7 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ X3 @ X0)
% 0.20/0.58          | ((k2_zfmisc_1 @ X4 @ X3) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | (r1_tarski @ X0 @ sk_C)
% 0.20/0.58          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | (r1_tarski @ X0 @ sk_C)
% 0.20/0.58          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_F @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['27', '36'])).
% 0.20/0.58  thf('38', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.58  thf('39', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain, (((sk_F) = (sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '40'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X6 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ X4)
% 0.20/0.58          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X4 @ X3))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ X4)
% 0.20/0.58          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '40'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | ((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X1))),
% 0.20/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.58  thf('50', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X1))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.20/0.58             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '52'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X6 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (((r1_tarski @ sk_A @ sk_D)
% 0.20/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf(t113_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((X3) = (k1_xboole_0))
% 0.20/0.58          | ((X4) = (k1_xboole_0))
% 0.20/0.58          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_A @ sk_D)
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_A @ sk_D))),
% 0.20/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.58  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('61', plain, ((r1_tarski @ sk_A @ sk_D)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['58', '59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('63', plain, ((~ (r1_tarski @ sk_D @ sk_A) | ((sk_D) = (sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.58  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '52'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.20/0.58           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.58  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '40'])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X6 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.58          | (r1_tarski @ X4 @ (k2_zfmisc_1 @ X2 @ X1))
% 0.20/0.58          | ((k2_zfmisc_1 @ X4 @ X3) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.58          | (r1_tarski @ X1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['70', '73'])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.58          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['69', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.20/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.20/0.58             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.58          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.58          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.58  thf('78', plain,
% 0.20/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.20/0.58           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['68', '77'])).
% 0.20/0.58  thf('79', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      ((r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      (((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['67', '80'])).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '52'])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X7 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      (((r1_tarski @ sk_B @ sk_E)
% 0.20/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((X3) = (k1_xboole_0))
% 0.20/0.58          | ((X4) = (k1_xboole_0))
% 0.20/0.58          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_B @ sk_E)
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_B @ sk_E))),
% 0.20/0.58      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.58  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('90', plain, ((r1_tarski @ sk_B @ sk_E)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['87', '88', '89'])).
% 0.20/0.58  thf('91', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('92', plain, ((~ (r1_tarski @ sk_E @ sk_B) | ((sk_E) = (sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.58  thf('93', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.58  thf('94', plain,
% 0.20/0.58      (((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['67', '80'])).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X7 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.20/0.58          | (r1_tarski @ X0 @ sk_B)
% 0.20/0.58          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_E @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['93', '96'])).
% 0.20/0.58  thf('98', plain,
% 0.20/0.58      (((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['67', '80'])).
% 0.20/0.58  thf('99', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((X3) = (k1_xboole_0))
% 0.20/0.58          | ((X4) = (k1_xboole_0))
% 0.20/0.58          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('100', plain,
% 0.20/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) != (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.58  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('103', plain, (((k2_zfmisc_1 @ sk_D @ sk_E) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['100', '101', '102'])).
% 0.20/0.58  thf('104', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['97', '103'])).
% 0.20/0.58  thf('105', plain, (((sk_E) = (sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['92', '104'])).
% 0.20/0.58  thf('106', plain,
% 0.20/0.58      (((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_E))),
% 0.20/0.58      inference('demod', [status(thm)], ['81', '105'])).
% 0.20/0.58  thf('107', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.20/0.58          | (r1_tarski @ X6 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.58  thf('108', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.20/0.58          | (r1_tarski @ X1 @ sk_A)
% 0.20/0.58          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.58  thf('109', plain,
% 0.20/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.58        | (r1_tarski @ sk_D @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['64', '108'])).
% 0.20/0.58  thf('110', plain, (((k2_zfmisc_1 @ sk_D @ sk_E) != (k1_xboole_0))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['100', '101', '102'])).
% 0.20/0.58  thf('111', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 0.20/0.58  thf('112', plain, (((sk_D) = (sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['63', '111'])).
% 0.20/0.58  thf('113', plain,
% 0.20/0.58      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('114', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.58      inference('split', [status(esa)], ['113'])).
% 0.20/0.58  thf('115', plain, (((sk_F) = (sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '39'])).
% 0.20/0.58  thf('116', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.58      inference('split', [status(esa)], ['113'])).
% 0.20/0.58  thf('117', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.58  thf('118', plain, ((((sk_C) = (sk_F)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['117'])).
% 0.20/0.58  thf('119', plain, (((sk_E) = (sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['92', '104'])).
% 0.20/0.58  thf('120', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.58      inference('split', [status(esa)], ['113'])).
% 0.20/0.58  thf('121', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.58  thf('122', plain, ((((sk_B) = (sk_E)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['121'])).
% 0.20/0.58  thf('123', plain,
% 0.20/0.58      (~ (((sk_A) = (sk_D))) | ~ (((sk_B) = (sk_E))) | ~ (((sk_C) = (sk_F)))),
% 0.20/0.58      inference('split', [status(esa)], ['113'])).
% 0.20/0.58  thf('124', plain, (~ (((sk_A) = (sk_D)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['118', '122', '123'])).
% 0.20/0.58  thf('125', plain, (((sk_A) != (sk_D))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['114', '124'])).
% 0.20/0.58  thf('126', plain, ($false),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['112', '125'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
