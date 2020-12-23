%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gm1bchsG91

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  180 (9634 expanded)
%              Number of leaves         :   16 (2745 expanded)
%              Depth                    :   43
%              Number of atoms          : 1626 (129434 expanded)
%              Number of equality atoms :  251 (18024 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t37_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ( ( k3_zfmisc_1 @ A @ B @ C )
            = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X3 @ X0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_C @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_C @ X0 )
      | ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ sk_F ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_F @ sk_C )
    | ( sk_F = sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('23',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X5 @ X4 @ X3 ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','29'])).

thf('31',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','29'])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( sk_C = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('41',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('45',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_E @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','29'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('49',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X3 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) )
      | ( sk_C = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('56',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('60',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ sk_B @ sk_E )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ sk_E )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_E ) ),
    inference('sup+',[status(thm)],['46','65'])).

thf('67',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('68',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ( sk_F = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_E @ sk_B )
    | ( sk_E = sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = sk_B )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','70'])).

thf('72',plain,
    ( ( sk_E = sk_B )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = sk_B ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_E = sk_B )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_E = sk_B )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = sk_B ) ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_E = sk_B ) ),
    inference('sup+',[status(thm)],['31','84'])).

thf('86',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('87',plain,(
    sk_E = sk_B ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['30','87'])).

thf('89',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('91',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('93',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ( sk_F = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('99',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
     != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','29'])).

thf('103',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('105',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ sk_A @ sk_D )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ sk_D )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('112',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,
    ( ( sk_F = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_D @ sk_A )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = sk_A )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','114'])).

thf('116',plain,
    ( ( sk_D = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    sk_E = sk_B ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('118',plain,
    ( ( sk_D = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    sk_F = sk_C ),
    inference(demod,[status(thm)],['21','28'])).

thf('122',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['119'])).

thf('123',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_E = sk_B ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('126',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['119'])).

thf('127',plain,
    ( ( sk_E != sk_E )
   <= ( sk_B != sk_E ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    sk_B = sk_E ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['119'])).

thf('130',plain,(
    sk_A != sk_D ),
    inference('sat_resolution*',[status(thm)],['124','128','129'])).

thf('131',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['120','130'])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['118','131'])).

thf('133',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('134',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('135',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('139',plain,
    ( ( r1_tarski @ sk_D @ sk_A )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( r1_tarski @ sk_D @ sk_A )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('141',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( sk_F = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_D @ sk_A )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('143',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = sk_A )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_D = sk_A )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['120','130'])).

thf('146',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','148'])).

thf('150',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('151',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('152',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != sk_E ),
    inference(demod,[status(thm)],['2','151'])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('154',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('159',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['152','160'])).

thf('162',plain,(
    $false ),
    inference(simplify,[status(thm)],['161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gm1bchsG91
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.63/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.81  % Solved by: fo/fo7.sh
% 0.63/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.81  % done 483 iterations in 0.331s
% 0.63/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.81  % SZS output start Refutation
% 0.63/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.63/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.63/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.81  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.63/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.81  thf(sk_E_type, type, sk_E: $i).
% 0.63/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.63/0.81  thf(sk_F_type, type, sk_F: $i).
% 0.63/0.81  thf(t37_mcart_1, conjecture,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.81     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.63/0.81       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.63/0.81         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.63/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.81    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.63/0.81        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.63/0.81          ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.63/0.81            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.63/0.81    inference('cnf.neg', [status(esa)], [t37_mcart_1])).
% 0.63/0.81  thf('0', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('1', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('2', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.81  thf('3', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(d10_xboole_0, axiom,
% 0.63/0.81    (![A:$i,B:$i]:
% 0.63/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.63/0.81  thf('4', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.63/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.81  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.81      inference('simplify', [status(thm)], ['4'])).
% 0.63/0.81  thf('6', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(d3_zfmisc_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i]:
% 0.63/0.81     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.63/0.81       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.63/0.81  thf('7', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf('8', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf(t138_zfmisc_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.81     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.63/0.81       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.63/0.81         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.63/0.81  thf('9', plain,
% 0.63/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.63/0.81         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0))
% 0.63/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.63/0.81          | (r1_tarski @ X10 @ X12))),
% 0.63/0.81      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.63/0.81  thf('10', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X3) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.63/0.81          | (r1_tarski @ X3 @ X0)
% 0.63/0.81          | ((k2_zfmisc_1 @ X4 @ X3) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.63/0.81  thf('11', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 0.63/0.81          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X0 @ X3))),
% 0.63/0.81      inference('sup-', [status(thm)], ['7', '10'])).
% 0.63/0.81  thf('12', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf('13', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 0.63/0.81          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X0 @ X3))),
% 0.63/0.81      inference('demod', [status(thm)], ['11', '12'])).
% 0.63/0.81  thf('14', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.63/0.81          | (r1_tarski @ sk_C @ X0)
% 0.63/0.81          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['6', '13'])).
% 0.63/0.81  thf('15', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('16', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.63/0.81          | (r1_tarski @ sk_C @ X0)
% 0.63/0.81          | ((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0)))),
% 0.63/0.81      inference('demod', [status(thm)], ['14', '15'])).
% 0.63/0.81  thf('17', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.81  thf('18', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.63/0.81          | (r1_tarski @ sk_C @ X0))),
% 0.63/0.81      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.63/0.81  thf('19', plain, ((r1_tarski @ sk_C @ sk_F)),
% 0.63/0.81      inference('sup-', [status(thm)], ['5', '18'])).
% 0.63/0.81  thf('20', plain,
% 0.63/0.81      (![X0 : $i, X2 : $i]:
% 0.63/0.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.63/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.81  thf('21', plain, ((~ (r1_tarski @ sk_F @ sk_C) | ((sk_F) = (sk_C)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.63/0.81  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.81      inference('simplify', [status(thm)], ['4'])).
% 0.63/0.81  thf('23', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('24', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X5 @ X4 @ X3))
% 0.63/0.81          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X0 @ X3))),
% 0.63/0.81      inference('demod', [status(thm)], ['11', '12'])).
% 0.63/0.81  thf('25', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.63/0.81             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.63/0.81          | (r1_tarski @ X0 @ sk_C)
% 0.63/0.81          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.63/0.81  thf('26', plain,
% 0.63/0.81      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.63/0.81        | (r1_tarski @ sk_F @ sk_C))),
% 0.63/0.81      inference('sup-', [status(thm)], ['22', '25'])).
% 0.63/0.81  thf('27', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.81  thf('28', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.63/0.81      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.63/0.81  thf('29', plain, (((sk_F) = (sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.81  thf('30', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('demod', [status(thm)], ['3', '29'])).
% 0.63/0.81  thf('31', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('demod', [status(thm)], ['3', '29'])).
% 0.63/0.81  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.81      inference('simplify', [status(thm)], ['4'])).
% 0.63/0.81  thf('33', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf('34', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('35', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf(t117_zfmisc_1, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i]:
% 0.63/0.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.63/0.81          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.63/0.81            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.63/0.81          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.63/0.81  thf('36', plain,
% 0.63/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.81         (((X6) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X7 @ X8)
% 0.63/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X6) @ (k2_zfmisc_1 @ X8 @ X6)))),
% 0.63/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.63/0.81  thf('37', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X3 @ X0) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.63/0.81          | (r1_tarski @ X3 @ (k2_zfmisc_1 @ X2 @ X1))
% 0.63/0.81          | ((X0) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['35', '36'])).
% 0.63/0.81  thf('38', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_C) @ 
% 0.63/0.81             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.63/0.81          | ((sk_C) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['34', '37'])).
% 0.63/0.81  thf('39', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_C) @ 
% 0.63/0.81             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.63/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.63/0.81          | ((sk_C) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['33', '38'])).
% 0.63/0.81  thf('40', plain, (((sk_F) = (sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.81  thf('41', plain, (((sk_F) = (sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.81  thf('42', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_F) @ 
% 0.63/0.81             (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.63/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.63/0.81          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.81      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.63/0.81  thf('43', plain,
% 0.63/0.81      ((((sk_F) = (k1_xboole_0))
% 0.63/0.81        | (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.63/0.81           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['32', '42'])).
% 0.63/0.81  thf('44', plain,
% 0.63/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.63/0.81         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0))
% 0.63/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.63/0.81          | (r1_tarski @ X10 @ X12))),
% 0.63/0.81      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.63/0.81  thf('45', plain,
% 0.63/0.81      ((((sk_F) = (k1_xboole_0))
% 0.63/0.81        | (r1_tarski @ sk_E @ sk_B)
% 0.63/0.81        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['43', '44'])).
% 0.63/0.81  thf('46', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('demod', [status(thm)], ['3', '29'])).
% 0.63/0.81  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.81      inference('simplify', [status(thm)], ['4'])).
% 0.63/0.81  thf('48', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf('49', plain,
% 0.63/0.81      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('50', plain,
% 0.63/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.81  thf('51', plain,
% 0.63/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.81         (((X6) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ X7 @ X8)
% 0.63/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X6) @ (k2_zfmisc_1 @ X8 @ X6)))),
% 0.63/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.63/0.81  thf('52', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X0))
% 0.63/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ X3)
% 0.63/0.81          | ((X0) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.63/0.81  thf('53', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.81             (k2_zfmisc_1 @ X0 @ sk_C))
% 0.63/0.81          | ((sk_C) = (k1_xboole_0))
% 0.63/0.81          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.63/0.81      inference('sup-', [status(thm)], ['49', '52'])).
% 0.63/0.81  thf('54', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.81             (k3_zfmisc_1 @ X1 @ X0 @ sk_C))
% 0.63/0.81          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.63/0.81          | ((sk_C) = (k1_xboole_0)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['48', '53'])).
% 0.63/0.81  thf('55', plain, (((sk_F) = (sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.81  thf('56', plain, (((sk_F) = (sk_C))),
% 0.63/0.81      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.81  thf('57', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         (~ (r1_tarski @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.63/0.82             (k3_zfmisc_1 @ X1 @ X0 @ sk_F))
% 0.63/0.82          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.63/0.82  thf('58', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.63/0.82           (k2_zfmisc_1 @ sk_D @ sk_E)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['47', '57'])).
% 0.63/0.82  thf('59', plain,
% 0.63/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.63/0.82         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0))
% 0.63/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.63/0.82          | (r1_tarski @ X10 @ X12))),
% 0.63/0.82      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.63/0.82  thf('60', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_B @ sk_E)
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['58', '59'])).
% 0.63/0.82  thf('61', plain,
% 0.63/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.82  thf('62', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.63/0.82          | (r1_tarski @ sk_B @ sk_E)
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['60', '61'])).
% 0.63/0.82  thf(t113_zfmisc_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.63/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.63/0.82  thf('63', plain,
% 0.63/0.82      (![X4 : $i, X5 : $i]:
% 0.63/0.82         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.63/0.82  thf('64', plain,
% 0.63/0.82      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.82  thf('65', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0))
% 0.63/0.82          | (r1_tarski @ sk_B @ sk_E)
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('demod', [status(thm)], ['62', '64'])).
% 0.63/0.82  thf('66', plain,
% 0.63/0.82      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_B @ sk_E))),
% 0.63/0.82      inference('sup+', [status(thm)], ['46', '65'])).
% 0.63/0.82  thf('67', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.82  thf('68', plain, ((((sk_F) = (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_E))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.63/0.82  thf('69', plain,
% 0.63/0.82      (![X0 : $i, X2 : $i]:
% 0.63/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.63/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.82  thf('70', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ~ (r1_tarski @ sk_E @ sk_B)
% 0.63/0.82        | ((sk_E) = (sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['68', '69'])).
% 0.63/0.82  thf('71', plain,
% 0.63/0.82      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (sk_B))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['45', '70'])).
% 0.63/0.82  thf('72', plain,
% 0.63/0.82      ((((sk_E) = (sk_B))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['71'])).
% 0.63/0.82  thf('73', plain,
% 0.63/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.82  thf('74', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.63/0.82          | ((sk_F) = (k1_xboole_0))
% 0.63/0.82          | ((sk_E) = (sk_B)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['72', '73'])).
% 0.63/0.82  thf('75', plain,
% 0.63/0.82      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.82  thf('76', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k1_xboole_0))
% 0.63/0.82          | ((sk_E) = (sk_B))
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['74', '75'])).
% 0.63/0.82  thf('77', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.82  thf('78', plain,
% 0.63/0.82      ((((k1_xboole_0) != (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['76', '77'])).
% 0.63/0.82  thf('79', plain, ((((sk_E) = (sk_B)) | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['78'])).
% 0.63/0.82  thf('80', plain,
% 0.63/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.82  thf('81', plain,
% 0.63/0.82      (![X4 : $i, X5 : $i]:
% 0.63/0.82         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.63/0.82  thf('82', plain,
% 0.63/0.82      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['81'])).
% 0.63/0.82  thf('83', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['80', '82'])).
% 0.63/0.82  thf('84', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0)) | ((sk_E) = (sk_B)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['79', '83'])).
% 0.63/0.82  thf('85', plain,
% 0.63/0.82      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (sk_B)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['31', '84'])).
% 0.63/0.82  thf('86', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.82  thf('87', plain, (((sk_E) = (sk_B))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('88', plain,
% 0.63/0.82      (((k3_zfmisc_1 @ sk_A @ sk_E @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.82      inference('demod', [status(thm)], ['30', '87'])).
% 0.63/0.82  thf('89', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.63/0.82           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['32', '42'])).
% 0.63/0.82  thf('90', plain,
% 0.63/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.63/0.82         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0))
% 0.63/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.63/0.82          | (r1_tarski @ X9 @ X11))),
% 0.63/0.82      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.63/0.82  thf('91', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['89', '90'])).
% 0.63/0.82  thf('92', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.63/0.82           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['32', '42'])).
% 0.63/0.82  thf('93', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.63/0.82           (k2_zfmisc_1 @ sk_D @ sk_E)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['47', '57'])).
% 0.63/0.82  thf('94', plain,
% 0.63/0.82      (![X0 : $i, X2 : $i]:
% 0.63/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.63/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.82  thf('95', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_D @ sk_E) @ 
% 0.63/0.82             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['93', '94'])).
% 0.63/0.82  thf('96', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['92', '95'])).
% 0.63/0.82  thf('97', plain,
% 0.63/0.82      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['96'])).
% 0.63/0.82  thf('98', plain,
% 0.63/0.82      (![X3 : $i, X4 : $i]:
% 0.63/0.82         (((X3) = (k1_xboole_0))
% 0.63/0.82          | ((X4) = (k1_xboole_0))
% 0.63/0.82          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.63/0.82  thf('99', plain,
% 0.63/0.82      ((((k2_zfmisc_1 @ sk_D @ sk_E) != (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['97', '98'])).
% 0.63/0.82  thf('100', plain,
% 0.63/0.82      ((((k1_xboole_0) != (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_B) = (k1_xboole_0))
% 0.63/0.82        | ((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['91', '99'])).
% 0.63/0.82  thf('101', plain,
% 0.63/0.82      ((((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_B) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['100'])).
% 0.63/0.82  thf('102', plain,
% 0.63/0.82      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.63/0.82      inference('demod', [status(thm)], ['3', '29'])).
% 0.63/0.82  thf('103', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.63/0.82           (k2_zfmisc_1 @ sk_D @ sk_E)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['47', '57'])).
% 0.63/0.82  thf('104', plain,
% 0.63/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.63/0.82         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0))
% 0.63/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X11 @ X12))
% 0.63/0.82          | (r1_tarski @ X9 @ X11))),
% 0.63/0.82      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.63/0.82  thf('105', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_A @ sk_D)
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['103', '104'])).
% 0.63/0.82  thf('106', plain,
% 0.63/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.82  thf('107', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.63/0.82          | (r1_tarski @ sk_A @ sk_D)
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['105', '106'])).
% 0.63/0.82  thf('108', plain,
% 0.63/0.82      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.82  thf('109', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0))
% 0.63/0.82          | (r1_tarski @ sk_A @ sk_D)
% 0.63/0.82          | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('demod', [status(thm)], ['107', '108'])).
% 0.63/0.82  thf('110', plain,
% 0.63/0.82      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_A @ sk_D))),
% 0.63/0.82      inference('sup+', [status(thm)], ['102', '109'])).
% 0.63/0.82  thf('111', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.82  thf('112', plain, ((((sk_F) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_D))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.63/0.82  thf('113', plain,
% 0.63/0.82      (![X0 : $i, X2 : $i]:
% 0.63/0.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.63/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.82  thf('114', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ~ (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_D) = (sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['112', '113'])).
% 0.63/0.82  thf('115', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_B) = (k1_xboole_0))
% 0.63/0.82        | ((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_D) = (sk_A))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['101', '114'])).
% 0.63/0.82  thf('116', plain,
% 0.63/0.82      ((((sk_D) = (sk_A))
% 0.63/0.82        | ((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_B) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['115'])).
% 0.63/0.82  thf('117', plain, (((sk_E) = (sk_B))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('118', plain,
% 0.63/0.82      ((((sk_D) = (sk_A))
% 0.63/0.82        | ((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('demod', [status(thm)], ['116', '117'])).
% 0.63/0.82  thf('119', plain,
% 0.63/0.82      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('120', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.63/0.82      inference('split', [status(esa)], ['119'])).
% 0.63/0.82  thf('121', plain, (((sk_F) = (sk_C))),
% 0.63/0.82      inference('demod', [status(thm)], ['21', '28'])).
% 0.63/0.82  thf('122', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.63/0.82      inference('split', [status(esa)], ['119'])).
% 0.63/0.82  thf('123', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['121', '122'])).
% 0.63/0.82  thf('124', plain, ((((sk_C) = (sk_F)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['123'])).
% 0.63/0.82  thf('125', plain, (((sk_E) = (sk_B))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('126', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.63/0.82      inference('split', [status(esa)], ['119'])).
% 0.63/0.82  thf('127', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['125', '126'])).
% 0.63/0.82  thf('128', plain, ((((sk_B) = (sk_E)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['127'])).
% 0.63/0.82  thf('129', plain,
% 0.63/0.82      (~ (((sk_A) = (sk_D))) | ~ (((sk_B) = (sk_E))) | ~ (((sk_C) = (sk_F)))),
% 0.63/0.82      inference('split', [status(esa)], ['119'])).
% 0.63/0.82  thf('130', plain, (~ (((sk_A) = (sk_D)))),
% 0.63/0.82      inference('sat_resolution*', [status(thm)], ['124', '128', '129'])).
% 0.63/0.82  thf('131', plain, (((sk_A) != (sk_D))),
% 0.63/0.82      inference('simpl_trail', [status(thm)], ['120', '130'])).
% 0.63/0.82  thf('132', plain,
% 0.63/0.82      ((((sk_A) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['118', '131'])).
% 0.63/0.82  thf('133', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['89', '90'])).
% 0.63/0.82  thf('134', plain,
% 0.63/0.82      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.82  thf('135', plain,
% 0.63/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.82         (((X6) = (k1_xboole_0))
% 0.63/0.82          | (r1_tarski @ X7 @ X8)
% 0.63/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X6) @ (k2_zfmisc_1 @ X8 @ X6)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.63/0.82  thf('136', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0)
% 0.63/0.82          | (r1_tarski @ X1 @ k1_xboole_0)
% 0.63/0.82          | ((X0) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['134', '135'])).
% 0.63/0.82  thf('137', plain,
% 0.63/0.82      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['133', '136'])).
% 0.63/0.82  thf('138', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.82      inference('simplify', [status(thm)], ['4'])).
% 0.63/0.82  thf('139', plain,
% 0.63/0.82      (((r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['137', '138'])).
% 0.63/0.82  thf('140', plain,
% 0.63/0.82      (((r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A))),
% 0.63/0.82      inference('sup+', [status(thm)], ['132', '139'])).
% 0.63/0.82  thf('141', plain,
% 0.63/0.82      ((((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0))
% 0.63/0.82        | (r1_tarski @ sk_D @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['140'])).
% 0.63/0.82  thf('142', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ~ (r1_tarski @ sk_D @ sk_A)
% 0.63/0.82        | ((sk_D) = (sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['112', '113'])).
% 0.63/0.82  thf('143', plain,
% 0.63/0.82      ((((sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0))
% 0.63/0.82        | ((sk_D) = (sk_A))
% 0.63/0.82        | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['141', '142'])).
% 0.63/0.82  thf('144', plain,
% 0.63/0.82      ((((sk_D) = (sk_A)) | ((sk_E) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify', [status(thm)], ['143'])).
% 0.63/0.82  thf('145', plain, (((sk_A) != (sk_D))),
% 0.63/0.82      inference('simpl_trail', [status(thm)], ['120', '130'])).
% 0.63/0.82  thf('146', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.63/0.82  thf('147', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['80', '82'])).
% 0.63/0.82  thf('148', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.63/0.82          | ((sk_E) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['146', '147'])).
% 0.63/0.82  thf('149', plain,
% 0.63/0.82      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.63/0.82        | ((sk_E) = (k1_xboole_0)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['88', '148'])).
% 0.63/0.82  thf('150', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.63/0.82  thf('151', plain, (((sk_E) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.63/0.82  thf('152', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_E))),
% 0.63/0.82      inference('demod', [status(thm)], ['2', '151'])).
% 0.63/0.82  thf('153', plain,
% 0.63/0.82      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['81'])).
% 0.63/0.82  thf('154', plain,
% 0.63/0.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.63/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.63/0.82  thf('155', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.63/0.82           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['153', '154'])).
% 0.63/0.82  thf('156', plain,
% 0.63/0.82      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.82  thf('157', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['155', '156'])).
% 0.63/0.82  thf('158', plain, (((sk_E) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.63/0.82  thf('159', plain, (((sk_E) = (k1_xboole_0))),
% 0.63/0.82      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 0.63/0.82  thf('160', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (sk_E))),
% 0.63/0.82      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.63/0.82  thf('161', plain, (((sk_E) != (sk_E))),
% 0.63/0.82      inference('demod', [status(thm)], ['152', '160'])).
% 0.63/0.82  thf('162', plain, ($false), inference('simplify', [status(thm)], ['161'])).
% 0.63/0.82  
% 0.63/0.82  % SZS output end Refutation
% 0.63/0.82  
% 0.63/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
