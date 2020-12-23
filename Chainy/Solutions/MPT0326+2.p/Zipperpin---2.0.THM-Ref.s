%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0326+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ofr90kL2RK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  418 ( 837 expanded)
%              Number of equality atoms :   42 (  62 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_13_type,type,(
    sk_C_13: $i )).

thf(sk_D_14_type,type,(
    sk_D_14: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t139_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ ( A @ B ) @ ( k2_zfmisc_1 @ ( C @ D ) ) ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ ( B @ A ) @ ( k2_zfmisc_1 @ ( D @ C ) ) ) ) )
         => ( r1_tarski @ ( B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ ( A @ B ) @ ( k2_zfmisc_1 @ ( C @ D ) ) ) )
              | ( r1_tarski @ ( k2_zfmisc_1 @ ( B @ A ) @ ( k2_zfmisc_1 @ ( D @ C ) ) ) ) )
           => ( r1_tarski @ ( B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_zfmisc_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( A @ B ) @ ( k2_zfmisc_1 @ ( C @ D ) ) ) )
     => ( ( ( k2_zfmisc_1 @ ( A @ B ) )
          = k1_xboole_0 )
        | ( ( r1_tarski @ ( A @ C ) )
          & ( r1_tarski @ ( B @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X1182: $i,X1183: $i,X1184: $i,X1185: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1182 @ X1183 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( X1182 @ X1183 ) @ ( k2_zfmisc_1 @ ( X1184 @ X1185 ) ) ) )
      | ( r1_tarski @ ( X1183 @ X1185 ) ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X1182: $i,X1183: $i,X1184: $i,X1185: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1182 @ X1183 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( X1182 @ X1183 ) @ ( k2_zfmisc_1 @ ( X1184 @ X1185 ) ) ) )
      | ( r1_tarski @ ( X1183 @ X1185 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) )
      | ( ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) )
        = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) )
      = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X1094: $i,X1095: $i] :
      ( ( X1094 = k1_xboole_0 )
      | ( X1095 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1095 @ X1094 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X1094: $i,X1095: $i] :
      ( ( X1094 = o_0_0_xboole_0 )
      | ( X1095 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1095 @ X1094 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 )
      | ( sk_B_4 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( sk_B_4 = o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ sk_D_14 ) )
      | ( sk_A_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('19',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_A_2 @ sk_B_4 ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ sk_D_14 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('28',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_C_13 ) ) ) ),
    inference(simpl_trail,[status(thm)],['2','28'])).

thf('30',plain,(
    ! [X1182: $i,X1183: $i,X1184: $i,X1185: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1182 @ X1183 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( X1182 @ X1183 ) @ ( k2_zfmisc_1 @ ( X1184 @ X1185 ) ) ) )
      | ( r1_tarski @ ( X1182 @ X1184 ) ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ! [X1182: $i,X1183: $i,X1184: $i,X1185: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1182 @ X1183 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( X1182 @ X1183 ) @ ( k2_zfmisc_1 @ ( X1184 @ X1185 ) ) ) )
      | ( r1_tarski @ ( X1182 @ X1184 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) )
    | ( ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_zfmisc_1 @ ( sk_B_4 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1094: $i,X1095: $i] :
      ( ( X1094 = o_0_0_xboole_0 )
      | ( X1095 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1095 @ X1094 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('37',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_B_4 = o_0_0_xboole_0 )
    | ( sk_A_2 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
    | ( sk_B_4 = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( sk_B_4 @ sk_D_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ sk_D_14 ) )
    | ( sk_A_2 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,(
    sk_A_2 = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42','43'])).

%------------------------------------------------------------------------------
