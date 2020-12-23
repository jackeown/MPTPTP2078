%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5svcsPdbTR

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 30.86s
% Output     : Refutation 30.86s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 235 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  927 (1890 expanded)
%              Number of equality atoms :   43 ( 117 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X56: $i] :
      ( ( k1_ordinal1 @ X56 )
      = ( k2_xboole_0 @ X56 @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X50 @ X49 )
      | ~ ( r1_tarski @ ( k2_tarski @ X48 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_tarski @ X48 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X47 @ X46 )
      | ( X46
        = ( k4_xboole_0 @ X46 @ ( k2_tarski @ X45 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('31',plain,(
    ! [X56: $i] :
      ( ( k1_ordinal1 @ X56 )
      = ( k2_xboole_0 @ X56 @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( zip_tseitin_0 @ X13 @ X12 @ X11 )
      | ( zip_tseitin_1 @ X13 @ X12 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ ( k1_tarski @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_tarski @ X0 ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
      | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( r2_hidden @ sk_B @ sk_B )
      | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
      | ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( zip_tseitin_1 @ X8 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,
    ( ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
      | ( r2_hidden @ sk_B @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('39',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_B @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('41',plain,
    ( ( ( r2_hidden @ sk_B @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( r2_hidden @ sk_B @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( r1_tarski @ X58 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('51',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('53',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['1','21'])).

thf('58',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('61',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_B @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('62',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ X53 @ X55 )
      | ( r1_tarski @ ( k1_setfam_1 @ X54 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ sk_B )
        | ( r2_hidden @ sk_A @ sk_B )
        | ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_B ) ) @ X0 )
        | ~ ( r1_tarski @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('64',plain,(
    ! [X52: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ sk_B )
        | ( r2_hidden @ sk_A @ sk_B )
        | ( r1_tarski @ sk_B @ X0 )
        | ~ ( r1_tarski @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( r1_tarski @ X58 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('70',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('75',plain,(
    ! [X56: $i] :
      ( ( k1_ordinal1 @ X56 )
      = ( k2_xboole_0 @ X56 @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('76',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('77',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ ( k2_tarski @ X48 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','73','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5svcsPdbTR
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 30.86/31.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.86/31.05  % Solved by: fo/fo7.sh
% 30.86/31.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.86/31.05  % done 28947 iterations in 30.582s
% 30.86/31.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.86/31.05  % SZS output start Refutation
% 30.86/31.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 30.86/31.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.86/31.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 30.86/31.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 30.86/31.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 30.86/31.05  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 30.86/31.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 30.86/31.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 30.86/31.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 30.86/31.05  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 30.86/31.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.86/31.05  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 30.86/31.05  thf(sk_B_type, type, sk_B: $i).
% 30.86/31.05  thf(sk_A_type, type, sk_A: $i).
% 30.86/31.05  thf(t13_ordinal1, conjecture,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 30.86/31.05       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 30.86/31.05  thf(zf_stmt_0, negated_conjecture,
% 30.86/31.05    (~( ![A:$i,B:$i]:
% 30.86/31.05        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 30.86/31.05          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 30.86/31.05    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 30.86/31.05  thf('0', plain,
% 30.86/31.05      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.86/31.05  thf('1', plain,
% 30.86/31.05      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['0'])).
% 30.86/31.05  thf(d1_ordinal1, axiom,
% 30.86/31.05    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 30.86/31.05  thf('2', plain,
% 30.86/31.05      (![X56 : $i]:
% 30.86/31.05         ((k1_ordinal1 @ X56) = (k2_xboole_0 @ X56 @ (k1_tarski @ X56)))),
% 30.86/31.05      inference('cnf', [status(esa)], [d1_ordinal1])).
% 30.86/31.05  thf(d10_xboole_0, axiom,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.86/31.05  thf('3', plain,
% 30.86/31.05      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 30.86/31.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.86/31.05  thf('4', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 30.86/31.05      inference('simplify', [status(thm)], ['3'])).
% 30.86/31.05  thf(t38_zfmisc_1, axiom,
% 30.86/31.05    (![A:$i,B:$i,C:$i]:
% 30.86/31.05     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 30.86/31.05       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 30.86/31.05  thf('5', plain,
% 30.86/31.05      (![X48 : $i, X49 : $i, X50 : $i]:
% 30.86/31.05         ((r2_hidden @ X50 @ X49)
% 30.86/31.05          | ~ (r1_tarski @ (k2_tarski @ X48 @ X50) @ X49))),
% 30.86/31.05      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 30.86/31.05  thf('6', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 30.86/31.05      inference('sup-', [status(thm)], ['4', '5'])).
% 30.86/31.05  thf(l49_zfmisc_1, axiom,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 30.86/31.05  thf('7', plain,
% 30.86/31.05      (![X41 : $i, X42 : $i]:
% 30.86/31.05         ((r1_tarski @ X41 @ (k3_tarski @ X42)) | ~ (r2_hidden @ X41 @ X42))),
% 30.86/31.05      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 30.86/31.05  thf('8', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['6', '7'])).
% 30.86/31.05  thf(l51_zfmisc_1, axiom,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 30.86/31.05  thf('9', plain,
% 30.86/31.05      (![X43 : $i, X44 : $i]:
% 30.86/31.05         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 30.86/31.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 30.86/31.05  thf('10', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 30.86/31.05      inference('demod', [status(thm)], ['8', '9'])).
% 30.86/31.05  thf('11', plain,
% 30.86/31.05      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 30.86/31.05      inference('sup+', [status(thm)], ['2', '10'])).
% 30.86/31.05  thf(t69_enumset1, axiom,
% 30.86/31.05    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 30.86/31.05  thf('12', plain,
% 30.86/31.05      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 30.86/31.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 30.86/31.05  thf('13', plain,
% 30.86/31.05      (![X48 : $i, X49 : $i, X50 : $i]:
% 30.86/31.05         ((r2_hidden @ X48 @ X49)
% 30.86/31.05          | ~ (r1_tarski @ (k2_tarski @ X48 @ X50) @ X49))),
% 30.86/31.05      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 30.86/31.05  thf('14', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 30.86/31.05      inference('sup-', [status(thm)], ['12', '13'])).
% 30.86/31.05  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 30.86/31.05      inference('sup-', [status(thm)], ['11', '14'])).
% 30.86/31.05  thf('16', plain,
% 30.86/31.05      ((((sk_A) = (sk_B))
% 30.86/31.05        | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.86/31.05  thf('17', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 30.86/31.05      inference('split', [status(esa)], ['16'])).
% 30.86/31.05  thf('18', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.86/31.05  thf('19', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('split', [status(esa)], ['18'])).
% 30.86/31.05  thf('20', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 30.86/31.05             (((sk_A) = (sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['17', '19'])).
% 30.86/31.05  thf('21', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['15', '20'])).
% 30.86/31.05  thf('22', plain,
% 30.86/31.05      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 30.86/31.05       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['18'])).
% 30.86/31.05  thf('23', plain,
% 30.86/31.05      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 30.86/31.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 30.86/31.05  thf(t144_zfmisc_1, axiom,
% 30.86/31.05    (![A:$i,B:$i,C:$i]:
% 30.86/31.05     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 30.86/31.05          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 30.86/31.05  thf('24', plain,
% 30.86/31.05      (![X45 : $i, X46 : $i, X47 : $i]:
% 30.86/31.05         ((r2_hidden @ X45 @ X46)
% 30.86/31.05          | (r2_hidden @ X47 @ X46)
% 30.86/31.05          | ((X46) = (k4_xboole_0 @ X46 @ (k2_tarski @ X45 @ X47))))),
% 30.86/31.05      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 30.86/31.05  thf('25', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 30.86/31.05          | (r2_hidden @ X0 @ X1)
% 30.86/31.05          | (r2_hidden @ X0 @ X1))),
% 30.86/31.05      inference('sup+', [status(thm)], ['23', '24'])).
% 30.86/31.05  thf('26', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         ((r2_hidden @ X0 @ X1)
% 30.86/31.05          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 30.86/31.05      inference('simplify', [status(thm)], ['25'])).
% 30.86/31.05  thf(t83_xboole_1, axiom,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 30.86/31.05  thf('27', plain,
% 30.86/31.05      (![X17 : $i, X19 : $i]:
% 30.86/31.05         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 30.86/31.05      inference('cnf', [status(esa)], [t83_xboole_1])).
% 30.86/31.05  thf('28', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (((X0) != (X0))
% 30.86/31.05          | (r2_hidden @ X1 @ X0)
% 30.86/31.05          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['26', '27'])).
% 30.86/31.05  thf('29', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 30.86/31.05      inference('simplify', [status(thm)], ['28'])).
% 30.86/31.05  thf('30', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('split', [status(esa)], ['16'])).
% 30.86/31.05  thf('31', plain,
% 30.86/31.05      (![X56 : $i]:
% 30.86/31.05         ((k1_ordinal1 @ X56) = (k2_xboole_0 @ X56 @ (k1_tarski @ X56)))),
% 30.86/31.05      inference('cnf', [status(esa)], [d1_ordinal1])).
% 30.86/31.05  thf(t5_xboole_0, axiom,
% 30.86/31.05    (![A:$i,B:$i,C:$i]:
% 30.86/31.05     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 30.86/31.05          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 30.86/31.05          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 30.86/31.05  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 30.86/31.05  thf(zf_stmt_2, axiom,
% 30.86/31.05    (![C:$i,B:$i,A:$i]:
% 30.86/31.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 30.86/31.05       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 30.86/31.05  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 30.86/31.05  thf(zf_stmt_4, axiom,
% 30.86/31.05    (![C:$i,B:$i,A:$i]:
% 30.86/31.05     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 30.86/31.05       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 30.86/31.05  thf(zf_stmt_5, axiom,
% 30.86/31.05    (![A:$i,B:$i,C:$i]:
% 30.86/31.05     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 30.86/31.05          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 30.86/31.05          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 30.86/31.05          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 30.86/31.05  thf('32', plain,
% 30.86/31.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 30.86/31.05         (~ (r1_xboole_0 @ X11 @ X12)
% 30.86/31.05          | (zip_tseitin_0 @ X13 @ X12 @ X11)
% 30.86/31.05          | (zip_tseitin_1 @ X13 @ X12 @ X11)
% 30.86/31.05          | ~ (r2_hidden @ X13 @ (k2_xboole_0 @ X11 @ X12)))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.86/31.05  thf('33', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 30.86/31.05          | (zip_tseitin_1 @ X1 @ (k1_tarski @ X0) @ X0)
% 30.86/31.05          | (zip_tseitin_0 @ X1 @ (k1_tarski @ X0) @ X0)
% 30.86/31.05          | ~ (r1_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['31', '32'])).
% 30.86/31.05  thf('34', plain,
% 30.86/31.05      (((~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_B))
% 30.86/31.05         | (zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 30.86/31.05         | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['30', '33'])).
% 30.86/31.05  thf('35', plain,
% 30.86/31.05      ((((r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 30.86/31.05         | (zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['29', '34'])).
% 30.86/31.05  thf('36', plain,
% 30.86/31.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 30.86/31.05         ((r2_hidden @ X8 @ X9) | ~ (zip_tseitin_1 @ X8 @ X10 @ X9))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 30.86/31.05  thf('37', plain,
% 30.86/31.05      ((((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['35', '36'])).
% 30.86/31.05  thf('38', plain,
% 30.86/31.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 30.86/31.05         ((r2_hidden @ X5 @ X6) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7))),
% 30.86/31.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.86/31.05  thf('39', plain,
% 30.86/31.05      ((((r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['37', '38'])).
% 30.86/31.05  thf('40', plain,
% 30.86/31.05      (![X41 : $i, X42 : $i]:
% 30.86/31.05         ((r1_tarski @ X41 @ (k3_tarski @ X42)) | ~ (r2_hidden @ X41 @ X42))),
% 30.86/31.05      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 30.86/31.05  thf('41', plain,
% 30.86/31.05      ((((r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['39', '40'])).
% 30.86/31.05  thf('42', plain,
% 30.86/31.05      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 30.86/31.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 30.86/31.05  thf('43', plain,
% 30.86/31.05      (![X43 : $i, X44 : $i]:
% 30.86/31.05         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 30.86/31.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 30.86/31.05  thf('44', plain,
% 30.86/31.05      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 30.86/31.05      inference('sup+', [status(thm)], ['42', '43'])).
% 30.86/31.05  thf(idempotence_k2_xboole_0, axiom,
% 30.86/31.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 30.86/31.05  thf('45', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 30.86/31.05      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 30.86/31.05  thf('46', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 30.86/31.05      inference('demod', [status(thm)], ['44', '45'])).
% 30.86/31.05  thf('47', plain,
% 30.86/31.05      ((((r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r1_tarski @ sk_A @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('demod', [status(thm)], ['41', '46'])).
% 30.86/31.05  thf(t7_ordinal1, axiom,
% 30.86/31.05    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.86/31.05  thf('48', plain,
% 30.86/31.05      (![X57 : $i, X58 : $i]:
% 30.86/31.05         (~ (r2_hidden @ X57 @ X58) | ~ (r1_tarski @ X58 @ X57))),
% 30.86/31.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 30.86/31.05  thf('49', plain,
% 30.86/31.05      ((((r1_tarski @ sk_A @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | ~ (r1_tarski @ sk_B @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['47', '48'])).
% 30.86/31.05  thf('50', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 30.86/31.05      inference('simplify', [status(thm)], ['3'])).
% 30.86/31.05  thf('51', plain,
% 30.86/31.05      ((((r1_tarski @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('demod', [status(thm)], ['49', '50'])).
% 30.86/31.05  thf('52', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['18'])).
% 30.86/31.05  thf('53', plain,
% 30.86/31.05      (((r1_tarski @ sk_A @ sk_B))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 30.86/31.05             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['51', '52'])).
% 30.86/31.05  thf('54', plain,
% 30.86/31.05      (![X14 : $i, X16 : $i]:
% 30.86/31.05         (((X14) = (X16))
% 30.86/31.05          | ~ (r1_tarski @ X16 @ X14)
% 30.86/31.05          | ~ (r1_tarski @ X14 @ X16))),
% 30.86/31.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.86/31.05  thf('55', plain,
% 30.86/31.05      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 30.86/31.05             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['53', '54'])).
% 30.86/31.05  thf('56', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 30.86/31.05      inference('split', [status(esa)], ['0'])).
% 30.86/31.05  thf('57', plain, (~ (((sk_A) = (sk_B)))),
% 30.86/31.05      inference('sat_resolution*', [status(thm)], ['1', '21'])).
% 30.86/31.05  thf('58', plain, (((sk_A) != (sk_B))),
% 30.86/31.05      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 30.86/31.05  thf('59', plain,
% 30.86/31.05      ((~ (r1_tarski @ sk_B @ sk_A))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 30.86/31.05             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('simplify_reflect-', [status(thm)], ['55', '58'])).
% 30.86/31.05  thf('60', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 30.86/31.05      inference('simplify', [status(thm)], ['3'])).
% 30.86/31.05  thf('61', plain,
% 30.86/31.05      ((((r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_B @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['37', '38'])).
% 30.86/31.05  thf(t8_setfam_1, axiom,
% 30.86/31.05    (![A:$i,B:$i,C:$i]:
% 30.86/31.05     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 30.86/31.05       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 30.86/31.05  thf('62', plain,
% 30.86/31.05      (![X53 : $i, X54 : $i, X55 : $i]:
% 30.86/31.05         (~ (r2_hidden @ X53 @ X54)
% 30.86/31.05          | ~ (r1_tarski @ X53 @ X55)
% 30.86/31.05          | (r1_tarski @ (k1_setfam_1 @ X54) @ X55))),
% 30.86/31.05      inference('cnf', [status(esa)], [t8_setfam_1])).
% 30.86/31.05  thf('63', plain,
% 30.86/31.05      ((![X0 : $i]:
% 30.86/31.05          ((r2_hidden @ sk_B @ sk_B)
% 30.86/31.05           | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05           | (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_B)) @ X0)
% 30.86/31.05           | ~ (r1_tarski @ sk_A @ X0)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['61', '62'])).
% 30.86/31.05  thf(t11_setfam_1, axiom,
% 30.86/31.05    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 30.86/31.05  thf('64', plain, (![X52 : $i]: ((k1_setfam_1 @ (k1_tarski @ X52)) = (X52))),
% 30.86/31.05      inference('cnf', [status(esa)], [t11_setfam_1])).
% 30.86/31.05  thf('65', plain,
% 30.86/31.05      ((![X0 : $i]:
% 30.86/31.05          ((r2_hidden @ sk_B @ sk_B)
% 30.86/31.05           | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05           | (r1_tarski @ sk_B @ X0)
% 30.86/31.05           | ~ (r1_tarski @ sk_A @ X0)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('demod', [status(thm)], ['63', '64'])).
% 30.86/31.05  thf('66', plain,
% 30.86/31.05      ((((r1_tarski @ sk_B @ sk_A)
% 30.86/31.05         | (r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r2_hidden @ sk_B @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['60', '65'])).
% 30.86/31.05  thf('67', plain,
% 30.86/31.05      (![X57 : $i, X58 : $i]:
% 30.86/31.05         (~ (r2_hidden @ X57 @ X58) | ~ (r1_tarski @ X58 @ X57))),
% 30.86/31.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 30.86/31.05  thf('68', plain,
% 30.86/31.05      ((((r2_hidden @ sk_A @ sk_B)
% 30.86/31.05         | (r1_tarski @ sk_B @ sk_A)
% 30.86/31.05         | ~ (r1_tarski @ sk_B @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['66', '67'])).
% 30.86/31.05  thf('69', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 30.86/31.05      inference('simplify', [status(thm)], ['3'])).
% 30.86/31.05  thf('70', plain,
% 30.86/31.05      ((((r2_hidden @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('demod', [status(thm)], ['68', '69'])).
% 30.86/31.05  thf('71', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['18'])).
% 30.86/31.05  thf('72', plain,
% 30.86/31.05      (((r1_tarski @ sk_B @ sk_A))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 30.86/31.05             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('sup-', [status(thm)], ['70', '71'])).
% 30.86/31.05  thf('73', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ sk_B)) | 
% 30.86/31.05       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('demod', [status(thm)], ['59', '72'])).
% 30.86/31.05  thf('74', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['16'])).
% 30.86/31.05  thf('75', plain,
% 30.86/31.05      (![X56 : $i]:
% 30.86/31.05         ((k1_ordinal1 @ X56) = (k2_xboole_0 @ X56 @ (k1_tarski @ X56)))),
% 30.86/31.05      inference('cnf', [status(esa)], [d1_ordinal1])).
% 30.86/31.05  thf('76', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 30.86/31.05      inference('simplify', [status(thm)], ['3'])).
% 30.86/31.05  thf('77', plain,
% 30.86/31.05      (![X48 : $i, X49 : $i, X50 : $i]:
% 30.86/31.05         ((r2_hidden @ X48 @ X49)
% 30.86/31.05          | ~ (r1_tarski @ (k2_tarski @ X48 @ X50) @ X49))),
% 30.86/31.05      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 30.86/31.05  thf('78', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 30.86/31.05      inference('sup-', [status(thm)], ['76', '77'])).
% 30.86/31.05  thf('79', plain,
% 30.86/31.05      (![X41 : $i, X42 : $i]:
% 30.86/31.05         ((r1_tarski @ X41 @ (k3_tarski @ X42)) | ~ (r2_hidden @ X41 @ X42))),
% 30.86/31.05      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 30.86/31.05  thf('80', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['78', '79'])).
% 30.86/31.05  thf('81', plain,
% 30.86/31.05      (![X43 : $i, X44 : $i]:
% 30.86/31.05         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 30.86/31.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 30.86/31.05  thf('82', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 30.86/31.05      inference('demod', [status(thm)], ['80', '81'])).
% 30.86/31.05  thf('83', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 30.86/31.05      inference('sup+', [status(thm)], ['75', '82'])).
% 30.86/31.05  thf(d3_tarski, axiom,
% 30.86/31.05    (![A:$i,B:$i]:
% 30.86/31.05     ( ( r1_tarski @ A @ B ) <=>
% 30.86/31.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 30.86/31.05  thf('84', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.86/31.05         (~ (r2_hidden @ X0 @ X1)
% 30.86/31.05          | (r2_hidden @ X0 @ X2)
% 30.86/31.05          | ~ (r1_tarski @ X1 @ X2))),
% 30.86/31.05      inference('cnf', [status(esa)], [d3_tarski])).
% 30.86/31.05  thf('85', plain,
% 30.86/31.05      (![X0 : $i, X1 : $i]:
% 30.86/31.05         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 30.86/31.05      inference('sup-', [status(thm)], ['83', '84'])).
% 30.86/31.05  thf('86', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 30.86/31.05         <= (((r2_hidden @ sk_A @ sk_B)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['74', '85'])).
% 30.86/31.05  thf('87', plain,
% 30.86/31.05      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 30.86/31.05         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 30.86/31.05      inference('split', [status(esa)], ['18'])).
% 30.86/31.05  thf('88', plain,
% 30.86/31.05      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 30.86/31.05       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 30.86/31.05      inference('sup-', [status(thm)], ['86', '87'])).
% 30.86/31.05  thf('89', plain,
% 30.86/31.05      (((r2_hidden @ sk_A @ sk_B)) | 
% 30.86/31.05       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | (((sk_A) = (sk_B)))),
% 30.86/31.05      inference('split', [status(esa)], ['16'])).
% 30.86/31.05  thf('90', plain, ($false),
% 30.86/31.05      inference('sat_resolution*', [status(thm)],
% 30.86/31.05                ['1', '21', '22', '73', '88', '89'])).
% 30.86/31.05  
% 30.86/31.05  % SZS output end Refutation
% 30.86/31.05  
% 30.86/31.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
