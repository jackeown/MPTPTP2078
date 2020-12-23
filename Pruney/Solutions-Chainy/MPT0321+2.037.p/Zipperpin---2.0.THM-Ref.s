%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zHZfXHjgMo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:37 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 500 expanded)
%              Number of leaves         :   19 ( 153 expanded)
%              Depth                    :   28
%              Number of atoms          :  771 (5343 expanded)
%              Number of equality atoms :   64 ( 609 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( k1_xboole_0 = sk_B )
    | ( k1_xboole_0 = sk_A ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_D @ sk_B )
    | ( r1_tarski @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('38',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X20 @ X18 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13'])).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('53',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('62',plain,
    ( ( sk_C_2 = sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('65',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['36','65'])).

thf('67',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['31','66'])).

thf('68',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['29','67'])).

thf('69',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('72',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['69'])).

thf('73',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A = sk_C_2 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['69'])).

thf('76',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['70','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zHZfXHjgMo
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.36/3.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.36/3.61  % Solved by: fo/fo7.sh
% 3.36/3.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.36/3.61  % done 2451 iterations in 3.153s
% 3.36/3.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.36/3.61  % SZS output start Refutation
% 3.36/3.61  thf(sk_D_type, type, sk_D: $i).
% 3.36/3.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.36/3.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.36/3.61  thf(sk_B_type, type, sk_B: $i).
% 3.36/3.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.36/3.61  thf(sk_A_type, type, sk_A: $i).
% 3.36/3.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.36/3.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.36/3.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.36/3.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.36/3.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.36/3.61  thf(t134_zfmisc_1, conjecture,
% 3.36/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.36/3.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.36/3.61         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 3.36/3.61  thf(zf_stmt_0, negated_conjecture,
% 3.36/3.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.61        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.36/3.61          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.36/3.61            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 3.36/3.61    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 3.36/3.61  thf('0', plain,
% 3.36/3.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf(t2_tarski, axiom,
% 3.36/3.61    (![A:$i,B:$i]:
% 3.36/3.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 3.36/3.61       ( ( A ) = ( B ) ) ))).
% 3.36/3.61  thf('1', plain,
% 3.36/3.61      (![X4 : $i, X5 : $i]:
% 3.36/3.61         (((X5) = (X4))
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 3.36/3.61      inference('cnf', [status(esa)], [t2_tarski])).
% 3.36/3.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.36/3.61  thf('2', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 3.36/3.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.36/3.61  thf(d3_tarski, axiom,
% 3.36/3.61    (![A:$i,B:$i]:
% 3.36/3.61     ( ( r1_tarski @ A @ B ) <=>
% 3.36/3.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.36/3.61  thf('3', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.61         (~ (r2_hidden @ X0 @ X1)
% 3.36/3.61          | (r2_hidden @ X0 @ X2)
% 3.36/3.61          | ~ (r1_tarski @ X1 @ X2))),
% 3.36/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.36/3.61  thf('4', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.36/3.61      inference('sup-', [status(thm)], ['2', '3'])).
% 3.36/3.61  thf('5', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 3.36/3.61          | ((k1_xboole_0) = (X0))
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 3.36/3.61      inference('sup-', [status(thm)], ['1', '4'])).
% 3.36/3.61  thf('6', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 3.36/3.61          | ((k1_xboole_0) = (X0)))),
% 3.36/3.61      inference('condensation', [status(thm)], ['5'])).
% 3.36/3.61  thf('7', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 3.36/3.61          | ((k1_xboole_0) = (X0)))),
% 3.36/3.61      inference('condensation', [status(thm)], ['5'])).
% 3.36/3.61  thf(l54_zfmisc_1, axiom,
% 3.36/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.61     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 3.36/3.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 3.36/3.61  thf('8', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 3.36/3.61         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 3.36/3.61          | ~ (r2_hidden @ X12 @ X14)
% 3.36/3.61          | ~ (r2_hidden @ X10 @ X11))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('9', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.61         (((k1_xboole_0) = (X0))
% 3.36/3.61          | ~ (r2_hidden @ X2 @ X1)
% 3.36/3.61          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X1 @ X0)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['7', '8'])).
% 3.36/3.61  thf('10', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         (((k1_xboole_0) = (X0))
% 3.36/3.61          | (r2_hidden @ 
% 3.36/3.61             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 3.36/3.61              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X0 @ X1))
% 3.36/3.61          | ((k1_xboole_0) = (X1)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['6', '9'])).
% 3.36/3.61  thf('11', plain,
% 3.36/3.61      (((r2_hidden @ 
% 3.36/3.61         (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 3.36/3.61          (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 3.36/3.61         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 3.36/3.61        | ((k1_xboole_0) = (sk_B))
% 3.36/3.61        | ((k1_xboole_0) = (sk_A)))),
% 3.36/3.61      inference('sup+', [status(thm)], ['0', '10'])).
% 3.36/3.61  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('14', plain,
% 3.36/3.61      ((r2_hidden @ 
% 3.36/3.61        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 3.36/3.61         (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 3.36/3.61        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('simplify_reflect-', [status(thm)], ['11', '12', '13'])).
% 3.36/3.61  thf('15', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.36/3.61         ((r2_hidden @ X10 @ X11)
% 3.36/3.61          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('16', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ k1_xboole_0) @ sk_C_2)),
% 3.36/3.61      inference('sup-', [status(thm)], ['14', '15'])).
% 3.36/3.61  thf('17', plain,
% 3.36/3.61      (![X1 : $i, X3 : $i]:
% 3.36/3.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.36/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.36/3.61  thf('18', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 3.36/3.61         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 3.36/3.61          | ~ (r2_hidden @ X12 @ X14)
% 3.36/3.61          | ~ (r2_hidden @ X10 @ X11))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('19', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.61         ((r1_tarski @ X0 @ X1)
% 3.36/3.61          | ~ (r2_hidden @ X3 @ X2)
% 3.36/3.61          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X2 @ X0)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['17', '18'])).
% 3.36/3.61  thf('20', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         ((r2_hidden @ 
% 3.36/3.61           (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ (sk_C @ X1 @ X0)) @ 
% 3.36/3.61           (k2_zfmisc_1 @ sk_C_2 @ X0))
% 3.36/3.61          | (r1_tarski @ X0 @ X1))),
% 3.36/3.61      inference('sup-', [status(thm)], ['16', '19'])).
% 3.36/3.61  thf('21', plain,
% 3.36/3.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('22', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.36/3.61         ((r2_hidden @ X12 @ X13)
% 3.36/3.61          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('23', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 3.36/3.61          | (r2_hidden @ X0 @ sk_B))),
% 3.36/3.61      inference('sup-', [status(thm)], ['21', '22'])).
% 3.36/3.61  thf('24', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B))),
% 3.36/3.61      inference('sup-', [status(thm)], ['20', '23'])).
% 3.36/3.61  thf('25', plain,
% 3.36/3.61      (![X1 : $i, X3 : $i]:
% 3.36/3.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.36/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.36/3.61  thf('26', plain, (((r1_tarski @ sk_D @ sk_B) | (r1_tarski @ sk_D @ sk_B))),
% 3.36/3.61      inference('sup-', [status(thm)], ['24', '25'])).
% 3.36/3.61  thf('27', plain, ((r1_tarski @ sk_D @ sk_B)),
% 3.36/3.61      inference('simplify', [status(thm)], ['26'])).
% 3.36/3.61  thf(d10_xboole_0, axiom,
% 3.36/3.61    (![A:$i,B:$i]:
% 3.36/3.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.36/3.61  thf('28', plain,
% 3.36/3.61      (![X6 : $i, X8 : $i]:
% 3.36/3.61         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 3.36/3.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.36/3.61  thf('29', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['27', '28'])).
% 3.36/3.61  thf('30', plain,
% 3.36/3.61      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 3.36/3.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.36/3.61  thf('31', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 3.36/3.61      inference('simplify', [status(thm)], ['30'])).
% 3.36/3.61  thf('32', plain,
% 3.36/3.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf(t117_zfmisc_1, axiom,
% 3.36/3.61    (![A:$i,B:$i,C:$i]:
% 3.36/3.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.36/3.61          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 3.36/3.61            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 3.36/3.61          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 3.36/3.61  thf('33', plain,
% 3.36/3.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.36/3.61         (((X15) = (k1_xboole_0))
% 3.36/3.61          | (r1_tarski @ X16 @ X17)
% 3.36/3.61          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 3.36/3.61               (k2_zfmisc_1 @ X15 @ X17)))),
% 3.36/3.61      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.36/3.61  thf('34', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 3.36/3.61             (k2_zfmisc_1 @ sk_A @ X0))
% 3.36/3.61          | (r1_tarski @ sk_B @ X0)
% 3.36/3.61          | ((sk_A) = (k1_xboole_0)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['32', '33'])).
% 3.36/3.61  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('36', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 3.36/3.61             (k2_zfmisc_1 @ sk_A @ X0))
% 3.36/3.61          | (r1_tarski @ sk_B @ X0))),
% 3.36/3.61      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 3.36/3.61  thf('37', plain,
% 3.36/3.61      (![X4 : $i, X5 : $i]:
% 3.36/3.61         (((X5) = (X4))
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 3.36/3.61      inference('cnf', [status(esa)], [t2_tarski])).
% 3.36/3.61  thf('38', plain, ((r1_tarski @ sk_D @ sk_B)),
% 3.36/3.61      inference('simplify', [status(thm)], ['26'])).
% 3.36/3.61  thf(t118_zfmisc_1, axiom,
% 3.36/3.61    (![A:$i,B:$i,C:$i]:
% 3.36/3.61     ( ( r1_tarski @ A @ B ) =>
% 3.36/3.61       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.36/3.61         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 3.36/3.61  thf('39', plain,
% 3.36/3.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.36/3.61         (~ (r1_tarski @ X18 @ X19)
% 3.36/3.61          | (r1_tarski @ (k2_zfmisc_1 @ X20 @ X18) @ (k2_zfmisc_1 @ X20 @ X19)))),
% 3.36/3.61      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.36/3.61  thf('40', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_B))),
% 3.36/3.61      inference('sup-', [status(thm)], ['38', '39'])).
% 3.36/3.61  thf('41', plain,
% 3.36/3.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('42', plain,
% 3.36/3.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.36/3.61         (((X15) = (k1_xboole_0))
% 3.36/3.61          | (r1_tarski @ X16 @ X17)
% 3.36/3.61          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 3.36/3.61               (k2_zfmisc_1 @ X17 @ X15)))),
% 3.36/3.61      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.36/3.61  thf('43', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X0 @ sk_B))
% 3.36/3.61          | (r1_tarski @ sk_A @ X0)
% 3.36/3.61          | ((sk_B) = (k1_xboole_0)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['41', '42'])).
% 3.36/3.61  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('45', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X0 @ sk_B))
% 3.36/3.61          | (r1_tarski @ sk_A @ X0))),
% 3.36/3.61      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 3.36/3.61  thf('46', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 3.36/3.61      inference('sup-', [status(thm)], ['40', '45'])).
% 3.36/3.61  thf('47', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.61         (~ (r2_hidden @ X0 @ X1)
% 3.36/3.61          | (r2_hidden @ X0 @ X2)
% 3.36/3.61          | ~ (r1_tarski @ X1 @ X2))),
% 3.36/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.36/3.61  thf('48', plain,
% 3.36/3.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 3.36/3.61      inference('sup-', [status(thm)], ['46', '47'])).
% 3.36/3.61  thf('49', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         ((r2_hidden @ (sk_C_1 @ sk_A @ X0) @ X0)
% 3.36/3.61          | ((X0) = (sk_A))
% 3.36/3.61          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_C_2))),
% 3.36/3.61      inference('sup-', [status(thm)], ['37', '48'])).
% 3.36/3.61  thf('50', plain,
% 3.36/3.61      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 3.36/3.61      inference('eq_fact', [status(thm)], ['49'])).
% 3.36/3.61  thf('51', plain,
% 3.36/3.61      ((r2_hidden @ 
% 3.36/3.61        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 3.36/3.61         (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 3.36/3.61        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('simplify_reflect-', [status(thm)], ['11', '12', '13'])).
% 3.36/3.61  thf('52', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.36/3.61         ((r2_hidden @ X12 @ X13)
% 3.36/3.61          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('53', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ k1_xboole_0) @ sk_D)),
% 3.36/3.61      inference('sup-', [status(thm)], ['51', '52'])).
% 3.36/3.61  thf('54', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 3.36/3.61         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 3.36/3.61          | ~ (r2_hidden @ X12 @ X14)
% 3.36/3.61          | ~ (r2_hidden @ X10 @ X11))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('55', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         (~ (r2_hidden @ X1 @ X0)
% 3.36/3.61          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 3.36/3.61             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['53', '54'])).
% 3.36/3.61  thf('56', plain,
% 3.36/3.61      ((((sk_C_2) = (sk_A))
% 3.36/3.61        | (r2_hidden @ 
% 3.36/3.61           (k4_tarski @ (sk_C_1 @ sk_A @ sk_C_2) @ 
% 3.36/3.61            (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 3.36/3.61           (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['50', '55'])).
% 3.36/3.61  thf('57', plain,
% 3.36/3.61      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('58', plain,
% 3.36/3.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.36/3.61         ((r2_hidden @ X10 @ X11)
% 3.36/3.61          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 3.36/3.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.36/3.61  thf('59', plain,
% 3.36/3.61      (![X0 : $i, X1 : $i]:
% 3.36/3.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 3.36/3.61          | (r2_hidden @ X1 @ sk_A))),
% 3.36/3.61      inference('sup-', [status(thm)], ['57', '58'])).
% 3.36/3.61  thf('60', plain,
% 3.36/3.61      ((((sk_C_2) = (sk_A)) | (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_A))),
% 3.36/3.61      inference('sup-', [status(thm)], ['56', '59'])).
% 3.36/3.61  thf('61', plain,
% 3.36/3.61      (![X4 : $i, X5 : $i]:
% 3.36/3.61         (((X5) = (X4))
% 3.36/3.61          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 3.36/3.61          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 3.36/3.61      inference('cnf', [status(esa)], [t2_tarski])).
% 3.36/3.61  thf('62', plain,
% 3.36/3.61      ((((sk_C_2) = (sk_A))
% 3.36/3.61        | ~ (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2)
% 3.36/3.61        | ((sk_C_2) = (sk_A)))),
% 3.36/3.61      inference('sup-', [status(thm)], ['60', '61'])).
% 3.36/3.61  thf('63', plain,
% 3.36/3.61      ((~ (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 3.36/3.61      inference('simplify', [status(thm)], ['62'])).
% 3.36/3.61  thf('64', plain,
% 3.36/3.61      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 3.36/3.61      inference('eq_fact', [status(thm)], ['49'])).
% 3.36/3.61  thf('65', plain, (((sk_C_2) = (sk_A))),
% 3.36/3.61      inference('clc', [status(thm)], ['63', '64'])).
% 3.36/3.61  thf('66', plain,
% 3.36/3.61      (![X0 : $i]:
% 3.36/3.61         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 3.36/3.61             (k2_zfmisc_1 @ sk_C_2 @ X0))
% 3.36/3.61          | (r1_tarski @ sk_B @ X0))),
% 3.36/3.61      inference('demod', [status(thm)], ['36', '65'])).
% 3.36/3.61  thf('67', plain, ((r1_tarski @ sk_B @ sk_D)),
% 3.36/3.61      inference('sup-', [status(thm)], ['31', '66'])).
% 3.36/3.61  thf('68', plain, (((sk_B) = (sk_D))),
% 3.36/3.61      inference('demod', [status(thm)], ['29', '67'])).
% 3.36/3.61  thf('69', plain, ((((sk_A) != (sk_C_2)) | ((sk_B) != (sk_D)))),
% 3.36/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.61  thf('70', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 3.36/3.61      inference('split', [status(esa)], ['69'])).
% 3.36/3.61  thf('71', plain, (((sk_C_2) = (sk_A))),
% 3.36/3.61      inference('clc', [status(thm)], ['63', '64'])).
% 3.36/3.61  thf('72', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 3.36/3.61      inference('split', [status(esa)], ['69'])).
% 3.36/3.61  thf('73', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 3.36/3.61      inference('sup-', [status(thm)], ['71', '72'])).
% 3.36/3.61  thf('74', plain, ((((sk_A) = (sk_C_2)))),
% 3.36/3.61      inference('simplify', [status(thm)], ['73'])).
% 3.36/3.61  thf('75', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C_2)))),
% 3.36/3.61      inference('split', [status(esa)], ['69'])).
% 3.36/3.61  thf('76', plain, (~ (((sk_B) = (sk_D)))),
% 3.36/3.61      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 3.36/3.61  thf('77', plain, (((sk_B) != (sk_D))),
% 3.36/3.61      inference('simpl_trail', [status(thm)], ['70', '76'])).
% 3.36/3.61  thf('78', plain, ($false),
% 3.36/3.61      inference('simplify_reflect-', [status(thm)], ['68', '77'])).
% 3.36/3.61  
% 3.36/3.61  % SZS output end Refutation
% 3.36/3.61  
% 3.44/3.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
