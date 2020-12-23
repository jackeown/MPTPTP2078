%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0877+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lhV1altGp9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 10.17s
% Output     : Refutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 289 expanded)
%              Number of leaves         :   13 (  91 expanded)
%              Depth                    :   26
%              Number of atoms          : 1009 (3217 expanded)
%              Number of equality atoms :  232 ( 714 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_76_type,type,(
    sk_B_76: $i )).

thf(sk_E_45_type,type,(
    sk_E_45: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_F_23_type,type,(
    sk_F_23: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(t37_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
        = ( k3_zfmisc_1 @ ( D @ ( E @ F ) ) ) )
     => ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
          = ( k3_zfmisc_1 @ ( D @ ( E @ F ) ) ) )
       => ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
            = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
        = ( k3_zfmisc_1 @ ( D @ ( E @ F ) ) ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('2',plain,(
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = k1_xboole_0 )
      | ( X3952 = k1_xboole_0 )
      | ( X3953 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3953 = X3954 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

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
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = o_0_0_xboole_0 )
      | ( X3952 = o_0_0_xboole_0 )
      | ( X3953 = o_0_0_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3953 = X3954 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
       != ( k3_zfmisc_1 @ ( X2 @ ( X1 @ X0 ) ) ) )
      | ( sk_A_14 = X2 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,
    ( ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = sk_D_93 ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A_14 != sk_D_93 )
    | ( sk_B_76 != sk_E_45 )
    | ( sk_C_93 != sk_F_23 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A_14 != sk_D_93 )
   <= ( sk_A_14 != sk_D_93 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = k1_xboole_0 )
      | ( X3952 = k1_xboole_0 )
      | ( X3953 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3951 = X3956 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = o_0_0_xboole_0 )
      | ( X3952 = o_0_0_xboole_0 )
      | ( X3953 = o_0_0_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3951 = X3956 ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
       != ( k3_zfmisc_1 @ ( X2 @ ( X1 @ X0 ) ) ) )
      | ( sk_C_93 = X0 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_C_93 = sk_F_23 ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_C_93 != sk_F_23 )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference(split,[status(esa)],['9'])).

thf('20',plain,
    ( ( ( sk_F_23 != sk_F_23 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_C_93 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ o_0_0_xboole_0 ) ) )
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
       != k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X3947: $i,X3948: $i,X3950: $i] :
      ( ( X3950 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3950 ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('25',plain,(
    ! [X3947: $i,X3948: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X3947: $i,X3948: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ o_0_0_xboole_0 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( o_0_0_xboole_0
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('simplify_reflect-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ sk_C_93 ) ) )
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3947: $i,X3948: $i,X3950: $i] :
      ( ( X3948 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3950 ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('39',plain,(
    ! [X3947: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( k1_xboole_0 @ X3950 ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    ! [X3947: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( o_0_0_xboole_0 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( o_0_0_xboole_0
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('45',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k3_zfmisc_1 @ ( o_0_0_xboole_0 @ ( sk_B_76 @ sk_C_93 ) ) )
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3947: $i,X3948: $i,X3950: $i] :
      ( ( X3947 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3950 ) ) )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('49',plain,(
    ! [X3948: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( k1_xboole_0 @ ( X3948 @ X3950 ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    ! [X3948: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X3948 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( o_0_0_xboole_0
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
   <= ( sk_C_93 != sk_F_23 ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('55',plain,(
    sk_C_93 = sk_F_23 ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = k1_xboole_0 )
      | ( X3952 = k1_xboole_0 )
      | ( X3953 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3952 = X3955 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    ! [X3951: $i,X3952: $i,X3953: $i,X3954: $i,X3955: $i,X3956: $i] :
      ( ( X3951 = o_0_0_xboole_0 )
      | ( X3952 = o_0_0_xboole_0 )
      | ( X3953 = o_0_0_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3953 @ ( X3952 @ X3951 ) ) )
       != ( k3_zfmisc_1 @ ( X3954 @ ( X3955 @ X3956 ) ) ) )
      | ( X3952 = X3955 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
       != ( k3_zfmisc_1 @ ( X2 @ ( X1 @ X0 ) ) ) )
      | ( sk_B_76 = X1 )
      | ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_C_93 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = sk_E_45 ) ),
    inference(eq_res,[status(thm)],['62'])).

thf('64',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ o_0_0_xboole_0 ) ) )
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_B_76 = sk_E_45 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3947: $i,X3948: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ o_0_0_xboole_0 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('67',plain,
    ( ( o_0_0_xboole_0
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_B_76 = sk_E_45 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('69',plain,
    ( ( sk_B_76 = sk_E_45 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B_76 != sk_E_45 )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference(split,[status(esa)],['9'])).

thf('71',plain,
    ( ( ( sk_E_45 != sk_E_45 )
      | ( sk_B_76 = o_0_0_xboole_0 )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( sk_A_14 = o_0_0_xboole_0 )
      | ( sk_B_76 = o_0_0_xboole_0 ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ sk_C_93 ) ) )
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3947: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( o_0_0_xboole_0 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('76',plain,
    ( ( ( o_0_0_xboole_0
        = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
      | ( sk_A_14 = o_0_0_xboole_0 ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('78',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k3_zfmisc_1 @ ( o_0_0_xboole_0 @ ( sk_B_76 @ sk_C_93 ) ) )
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3948: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X3948 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('82',plain,
    ( ( o_0_0_xboole_0
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
   <= ( sk_B_76 != sk_E_45 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('84',plain,(
    sk_B_76 = sk_E_45 ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_A_14 != sk_D_93 )
    | ( sk_B_76 != sk_E_45 )
    | ( sk_C_93 != sk_F_23 ) ),
    inference(split,[status(esa)],['9'])).

thf('86',plain,(
    sk_A_14 != sk_D_93 ),
    inference('sat_resolution*',[status(thm)],['55','84','85'])).

thf('87',plain,(
    sk_A_14 != sk_D_93 ),
    inference(simpl_trail,[status(thm)],['10','86'])).

thf('88',plain,
    ( ( sk_C_93 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['8','87'])).

thf('89',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ o_0_0_xboole_0 ) ) )
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X3947: $i,X3948: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ o_0_0_xboole_0 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('92',plain,
    ( ( o_0_0_xboole_0
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('94',plain,
    ( ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_B_76 @ sk_C_93 ) ) )
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( o_0_0_xboole_0 @ sk_C_93 ) ) )
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X3947: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( X3947 @ ( o_0_0_xboole_0 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('98',plain,
    ( ( o_0_0_xboole_0
      = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('100',plain,(
    sk_A_14 = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X3948: $i,X3950: $i] :
      ( ( k3_zfmisc_1 @ ( o_0_0_xboole_0 @ ( X3948 @ X3950 ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('102',plain,
    ( o_0_0_xboole_0
    = ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) ) ),
    inference(demod,[status(thm)],['0','100','101'])).

thf('103',plain,(
    ( k3_zfmisc_1 @ ( sk_D_93 @ ( sk_E_45 @ sk_F_23 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
