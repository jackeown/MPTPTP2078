%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0321+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nvW1yEQJq6

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:42 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 742 expanded)
%              Number of leaves         :   19 ( 228 expanded)
%              Depth                    :   29
%              Number of atoms          :  916 (7317 expanded)
%              Number of equality atoms :  100 (1176 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( X9 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( X9 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['9','12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('18',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ X0 )
      | ( X0 = sk_D )
      | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_D = o_0_0_xboole_0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['9','12','15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('40',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('49',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('52',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_D = o_0_0_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['9','12','15'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('58',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('62',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('63',plain,(
    sk_A = sk_C_1 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 != sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('65',plain,(
    sk_B_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['29','65'])).

thf('67',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['27','66'])).

thf('68',plain,(
    ! [X9: $i] :
      ( ( X9 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X2 ) @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X2 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X2 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X2 ) @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = sk_D )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['29','65'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','78'])).

thf('80',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('81',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('83',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['27','66'])).

thf('87',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['29','65'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).


%------------------------------------------------------------------------------
