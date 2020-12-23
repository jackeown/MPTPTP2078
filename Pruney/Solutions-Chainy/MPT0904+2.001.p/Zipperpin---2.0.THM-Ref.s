%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ochMxy7PpD

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  674 (1328 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t64_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ~ ( r1_xboole_0 @ A @ E )
        & ~ ( r1_xboole_0 @ B @ F )
        & ~ ( r1_xboole_0 @ C @ G )
        & ~ ( r1_xboole_0 @ D @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ~ ( r1_xboole_0 @ A @ E )
          & ~ ( r1_xboole_0 @ B @ F )
          & ~ ( r1_xboole_0 @ C @ G )
          & ~ ( r1_xboole_0 @ D @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_mcart_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_G )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['3'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('6',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_G ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X2 @ sk_G ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_C ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_G ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('10',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_C ) @ X5 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_G ) @ X4 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('13',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ sk_C @ X5 ) @ ( k4_zfmisc_1 @ X1 @ X0 @ sk_G @ X4 ) )
   <= ( r1_xboole_0 @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_E )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('16',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_E @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('18',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ X0 ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ X1 @ X3 ) @ ( k3_zfmisc_1 @ sk_E @ X0 @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ X3 @ X2 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ X1 @ X0 ) @ X4 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('26',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ X3 @ X2 @ X5 ) @ ( k4_zfmisc_1 @ sk_E @ X1 @ X0 @ X4 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_H )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X3 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D ) @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H ) )
   <= ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_H ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_F )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('42',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_F ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('45',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ sk_B @ X3 ) @ ( k3_zfmisc_1 @ X0 @ sk_F @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('47',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ sk_B @ X2 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ sk_F @ X0 ) @ X4 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('50',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
        ( r1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ sk_B @ X2 @ X5 ) @ ( k4_zfmisc_1 @ X1 @ sk_F @ X0 @ X4 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_F ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_G )
    | ( r1_xboole_0 @ sk_B @ sk_F )
    | ( r1_xboole_0 @ sk_D @ sk_H )
    | ( r1_xboole_0 @ sk_A @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,(
    r1_xboole_0 @ sk_C @ sk_G ),
    inference('sat_resolution*',[status(thm)],['28','37','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ sk_C @ X5 ) @ ( k4_zfmisc_1 @ X1 @ X0 @ sk_G @ X4 ) ) ),
    inference(simpl_trail,[status(thm)],['13','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ochMxy7PpD
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 173 iterations in 0.091s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(sk_H_type, type, sk_H: $i).
% 0.36/0.54  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.54  thf(t64_mcart_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.54     ( ( ~( r1_xboole_0 @
% 0.36/0.54            ( k4_zfmisc_1 @ A @ B @ C @ D ) @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.36/0.54       ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.36/0.54         ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.54        ( ( ~( r1_xboole_0 @
% 0.36/0.54               ( k4_zfmisc_1 @ A @ B @ C @ D ) @ 
% 0.36/0.54               ( k4_zfmisc_1 @ E @ F @ G @ H ) ) ) =>
% 0.36/0.54          ( ( ~( r1_xboole_0 @ A @ E ) ) & ( ~( r1_xboole_0 @ B @ F ) ) & 
% 0.36/0.54            ( ~( r1_xboole_0 @ C @ G ) ) & ( ~( r1_xboole_0 @ D @ H ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t64_mcart_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.36/0.54          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d3_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_A @ sk_E)
% 0.36/0.54        | (r1_xboole_0 @ sk_B @ sk_F)
% 0.36/0.54        | (r1_xboole_0 @ sk_C @ sk_G)
% 0.36/0.54        | (r1_xboole_0 @ sk_D @ sk_H))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_C @ sk_G)) <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('split', [status(esa)], ['3'])).
% 0.36/0.54  thf(t127_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.36/0.54       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_G)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ sk_C) @ 
% 0.36/0.54           (k2_zfmisc_1 @ X2 @ sk_G)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['2', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ sk_C) @ 
% 0.36/0.54           (k3_zfmisc_1 @ X1 @ X0 @ sk_G)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['1', '7'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ sk_C) @ X5) @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ X0 @ sk_G) @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf(d4_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.36/0.54       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ sk_C @ X5) @ 
% 0.36/0.54           (k4_zfmisc_1 @ X1 @ X0 @ sk_G @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_C @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_A @ sk_E)) <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('split', [status(esa)], ['3'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_E @ X0)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X3) @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ X0) @ X2)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ X1 @ X3) @ 
% 0.36/0.54           (k3_zfmisc_1 @ sk_E @ X0 @ X2)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ X3 @ X2) @ X5) @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ X1 @ X0) @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ X3 @ X2 @ X5) @ 
% 0.36/0.54           (k4_zfmisc_1 @ sk_E @ X1 @ X0 @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_A @ sk_E)))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.36/0.54          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain, (~ ((r1_xboole_0 @ sk_A @ sk_E))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_D @ sk_H)) <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.36/0.54      inference('split', [status(esa)], ['3'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_H)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_D) @ 
% 0.36/0.54           (k2_zfmisc_1 @ X3 @ sk_H)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['30', '33'])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k4_zfmisc_1 @ X5 @ X4 @ X3 @ sk_D) @ 
% 0.36/0.54           (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_D @ sk_H)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['29', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.36/0.54          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('37', plain, (~ ((r1_xboole_0 @ sk_D @ sk_H))),
% 0.36/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_B @ sk_F)) <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('split', [status(esa)], ['3'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_F)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B) @ X3) @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_F) @ X2)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k3_zfmisc_1 @ X1 @ sk_B @ X3) @ 
% 0.36/0.54           (k3_zfmisc_1 @ X0 @ sk_F @ X2)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ sk_B @ X2) @ X5) @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ sk_F @ X0) @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54          (r1_xboole_0 @ (k4_zfmisc_1 @ X3 @ sk_B @ X2 @ X5) @ 
% 0.36/0.54           (k4_zfmisc_1 @ X1 @ sk_F @ X0 @ X4)))
% 0.36/0.54         <= (((r1_xboole_0 @ sk_B @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.36/0.54          (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('52', plain, (~ ((r1_xboole_0 @ sk_B @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (((r1_xboole_0 @ sk_C @ sk_G)) | ((r1_xboole_0 @ sk_B @ sk_F)) | 
% 0.36/0.54       ((r1_xboole_0 @ sk_D @ sk_H)) | ((r1_xboole_0 @ sk_A @ sk_E))),
% 0.36/0.54      inference('split', [status(esa)], ['3'])).
% 0.36/0.54  thf('54', plain, (((r1_xboole_0 @ sk_C @ sk_G))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['28', '37', '52', '53'])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (r1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ sk_C @ X5) @ 
% 0.36/0.54          (k4_zfmisc_1 @ X1 @ X0 @ sk_G @ X4))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['13', '54'])).
% 0.36/0.54  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
