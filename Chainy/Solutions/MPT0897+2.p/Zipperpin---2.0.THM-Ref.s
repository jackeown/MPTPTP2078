%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0897+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W3khHPAWRD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 15.46s
% Output     : Refutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 487 expanded)
%              Number of leaves         :   15 ( 152 expanded)
%              Depth                    :   32
%              Number of atoms          : 1832 (6515 expanded)
%              Number of equality atoms :  393 (1366 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_G_9_type,type,(
    sk_G_9: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_27_type,type,(
    sk_F_27: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_46_type,type,(
    sk_E_46: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_B_78_type,type,(
    sk_B_78: $i )).

thf(sk_H_6_type,type,(
    sk_H_6: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(t57_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k4_zfmisc_1 @ ( E @ ( F @ ( G @ H ) ) ) ) )
     => ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
          = ( k4_zfmisc_1 @ ( E @ ( F @ ( G @ H ) ) ) ) )
       => ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
            = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k4_zfmisc_1 @ ( E @ ( F @ ( G @ H ) ) ) ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( D = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('2',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = k1_xboole_0 )
      | ( X4094 = k1_xboole_0 )
      | ( X4095 = k1_xboole_0 )
      | ( X4096 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4093 = X4100 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = o_0_0_xboole_0 )
      | ( X4094 = o_0_0_xboole_0 )
      | ( X4095 = o_0_0_xboole_0 )
      | ( X4096 = o_0_0_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4093 = X4100 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_D_93 = X0 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_D_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( sk_D_93 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_D_93 = sk_H_6 ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A_14 != sk_E_46 )
    | ( sk_B_78 != sk_F_27 )
    | ( sk_C_93 != sk_G_9 )
    | ( sk_D_93 != sk_H_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_D_93 != sk_H_6 )
   <= ( sk_D_93 != sk_H_6 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = k1_xboole_0 )
      | ( X4094 = k1_xboole_0 )
      | ( X4095 = k1_xboole_0 )
      | ( X4096 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4095 = X4098 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = o_0_0_xboole_0 )
      | ( X4094 = o_0_0_xboole_0 )
      | ( X4095 = o_0_0_xboole_0 )
      | ( X4096 = o_0_0_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4095 = X4098 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_B_78 = X2 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_D_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( sk_D_93 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = sk_F_27 ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ o_0_0_xboole_0 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = sk_F_27 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
       != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4092: $i] :
      ( ( X4092 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ k1_xboole_0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ o_0_0_xboole_0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = sk_F_27 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_78 = sk_F_27 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( o_0_0_xboole_0 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = sk_F_27 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4092: $i] :
      ( ( X4090 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('38',plain,(
    ! [X4088: $i,X4089: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( k1_xboole_0 @ X4092 ) ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    ! [X4088: $i,X4089: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( o_0_0_xboole_0 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = sk_F_27 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('44',plain,
    ( ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = sk_F_27 ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_78 != sk_F_27 )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference(split,[status(esa)],['10'])).

thf('46',plain,
    ( ( ( sk_F_27 != sk_F_27 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ ( sk_C_93 @ sk_D_93 ) ) ) )
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4092: $i] :
      ( ( X4089 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('51',plain,(
    ! [X4088: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( k1_xboole_0 @ ( X4090 @ X4092 ) ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('54',plain,(
    ! [X4088: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( o_0_0_xboole_0 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( o_0_0_xboole_0
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('57',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4092: $i] :
      ( ( X4088 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('61',plain,(
    ! [X4089: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( k1_xboole_0 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X4089: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_B_78 != sk_F_27 ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('67',plain,(
    sk_B_78 = sk_F_27 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = k1_xboole_0 )
      | ( X4094 = k1_xboole_0 )
      | ( X4095 = k1_xboole_0 )
      | ( X4096 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4096 = X4097 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('70',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('73',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('74',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = o_0_0_xboole_0 )
      | ( X4094 = o_0_0_xboole_0 )
      | ( X4095 = o_0_0_xboole_0 )
      | ( X4096 = o_0_0_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4096 = X4097 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_A_14 = X3 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_D_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( sk_D_93 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = sk_E_46 ) ),
    inference(eq_res,[status(thm)],['75'])).

thf('77',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ o_0_0_xboole_0 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ o_0_0_xboole_0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('80',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,
    ( ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( o_0_0_xboole_0 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = sk_E_46 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4088: $i,X4089: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( o_0_0_xboole_0 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('86',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = sk_E_46 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('88',plain,
    ( ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = sk_E_46 ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ ( sk_C_93 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X4088: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( o_0_0_xboole_0 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('92',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('94',plain,
    ( ( sk_A_14 = sk_E_46 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_A_14 != sk_E_46 )
   <= ( sk_A_14 != sk_E_46 ) ),
    inference(split,[status(esa)],['10'])).

thf('96',plain,
    ( ( ( sk_E_46 != sk_E_46 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_A_14 != sk_E_46 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
   <= ( sk_A_14 != sk_E_46 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_A_14 != sk_E_46 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4089: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('101',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_A_14 != sk_E_46 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('103',plain,(
    sk_A_14 = sk_E_46 ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = k1_xboole_0 )
      | ( X4094 = k1_xboole_0 )
      | ( X4095 = k1_xboole_0 )
      | ( X4096 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4094 = X4099 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('106',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('107',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('108',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('109',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('110',plain,(
    ! [X4093: $i,X4094: $i,X4095: $i,X4096: $i,X4097: $i,X4098: $i,X4099: $i,X4100: $i] :
      ( ( X4093 = o_0_0_xboole_0 )
      | ( X4094 = o_0_0_xboole_0 )
      | ( X4095 = o_0_0_xboole_0 )
      | ( X4096 = o_0_0_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4096 @ ( X4095 @ ( X4094 @ X4093 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4097 @ ( X4098 @ ( X4099 @ X4100 ) ) ) ) )
      | ( X4094 = X4099 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_C_93 = X1 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_D_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ( sk_D_93 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_C_93 = sk_G_9 ) ),
    inference(eq_res,[status(thm)],['111'])).

thf('113',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ o_0_0_xboole_0 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_C_93 = sk_G_9 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ o_0_0_xboole_0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('116',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_C_93 = sk_G_9 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('118',plain,
    ( ( sk_C_93 = sk_G_9 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C_93 != sk_G_9 )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference(split,[status(esa)],['10'])).

thf('120',plain,
    ( ( ( sk_G_9 != sk_G_9 )
      | ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( o_0_0_xboole_0 @ sk_D_93 ) ) ) )
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X4088: $i,X4089: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( o_0_0_xboole_0 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('125',plain,
    ( ( ( o_0_0_xboole_0
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('127',plain,
    ( ( ( sk_B_78 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ ( sk_C_93 @ sk_D_93 ) ) ) )
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X4088: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( o_0_0_xboole_0 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('131',plain,
    ( ( ( o_0_0_xboole_0
        = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('133',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X4089: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('137',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
   <= ( sk_C_93 != sk_G_9 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('139',plain,(
    sk_C_93 = sk_G_9 ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_D_93 != sk_H_6 )
    | ( sk_C_93 != sk_G_9 )
    | ( sk_A_14 != sk_E_46 )
    | ( sk_B_78 != sk_F_27 ) ),
    inference(split,[status(esa)],['10'])).

thf('141',plain,(
    sk_D_93 != sk_H_6 ),
    inference('sat_resolution*',[status(thm)],['67','103','139','140'])).

thf('142',plain,(
    sk_D_93 != sk_H_6 ),
    inference(simpl_trail,[status(thm)],['11','141'])).

thf('143',plain,
    ( ( sk_D_93 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['9','142'])).

thf('144',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ o_0_0_xboole_0 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ o_0_0_xboole_0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('147',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('149',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_C_93 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( o_0_0_xboole_0 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X4088: $i,X4089: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( o_0_0_xboole_0 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('153',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('155',plain,
    ( ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_B_78 @ ( sk_C_93 @ sk_D_93 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ ( sk_C_93 @ sk_D_93 ) ) ) )
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X4088: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( X4088 @ ( o_0_0_xboole_0 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('159',plain,
    ( ( o_0_0_xboole_0
      = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('161',plain,(
    sk_A_14 = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X4089: $i,X4090: $i,X4092: $i] :
      ( ( k4_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X4089 @ ( X4090 @ X4092 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('163',plain,
    ( o_0_0_xboole_0
    = ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) ) ),
    inference(demod,[status(thm)],['0','161','162'])).

thf('164',plain,(
    ( k4_zfmisc_1 @ ( sk_E_46 @ ( sk_F_27 @ ( sk_G_9 @ sk_H_6 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('165',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

%------------------------------------------------------------------------------
