%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0321+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i0nFxWE5L9

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:42 EST 2020

% Result     : Theorem 22.14s
% Output     : Refutation 22.14s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 962 expanded)
%              Number of leaves         :   17 ( 295 expanded)
%              Depth                    :   29
%              Number of atoms          : 1107 (9567 expanded)
%              Number of equality atoms :  137 (1554 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( X10 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( X10 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['8','11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ X0 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ X0 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1 = sk_A ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['8','11','14'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C_1 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_C_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C_1 = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('39',plain,
    ( ( sk_C_1 = sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1 = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1 = sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1 = sk_A ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('42',plain,(
    sk_C_1 = sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['17','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( X10 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X1 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X2 = X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ X0 )
      | ( X0 = sk_D )
      | ( sk_C_1 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,(
    sk_C_1 = sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('55',plain,(
    sk_C_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ X0 )
      | ( X0 = sk_D )
      | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_B_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_D = o_0_0_xboole_0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['8','11','14'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('66',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('73',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('75',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('78',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('80',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_D = o_0_0_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('85',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('86',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = o_0_0_xboole_0 )
      | ( X6 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
     != o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('90',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('91',plain,(
    ( k2_zfmisc_1 @ sk_C_1 @ sk_D )
 != o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('94',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('96',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( sk_B_1 != sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('101',plain,(
    sk_B_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['59','101'])).

thf('103',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['57','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','105'])).

thf('107',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_C_1 = sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('109',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('112',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('114',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['57','102'])).

thf('116',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    sk_B_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['59','101'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).


%------------------------------------------------------------------------------
