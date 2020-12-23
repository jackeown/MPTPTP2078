%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96DTckP9bY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 425 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   24
%              Number of atoms          :  812 (4684 expanded)
%              Number of equality atoms :   42 ( 307 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X13
        = ( k4_xboole_0 @ X13 @ ( k2_tarski @ X12 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('26',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X13
        = ( k4_xboole_0 @ X13 @ ( k2_tarski @ X12 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X18 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('50',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('55',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['47','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('61',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X18 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( sk_B
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','66'])).

thf('68',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('69',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['51'])).

thf('70',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['53','69'])).

thf('71',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['67','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('74',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('76',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['47','55'])).

thf('78',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('80',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96DTckP9bY
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 534 iterations in 0.327s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.77  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.58/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.77  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(t15_mcart_1, conjecture,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.58/0.77       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.58/0.77         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.58/0.77          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.58/0.77            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t10_mcart_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.58/0.77       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.58/0.77         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.77         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.58/0.77          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(d5_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.77       ( ![D:$i]:
% 0.58/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.77          | (r2_hidden @ X0 @ X2)
% 0.58/0.77          | (r2_hidden @ X0 @ X3)
% 0.58/0.77          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.77          | (r2_hidden @ X0 @ X2)
% 0.58/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.58/0.77          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.58/0.77             (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '4'])).
% 0.58/0.77  thf(t64_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.58/0.77       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.77         (((X15) != (X17))
% 0.58/0.77          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17))))),
% 0.58/0.77      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i]:
% 0.58/0.77         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(t144_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.58/0.77          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.77         ((r2_hidden @ X12 @ X13)
% 0.58/0.77          | (r2_hidden @ X14 @ X13)
% 0.58/0.77          | ((X13) = (k4_xboole_0 @ X13 @ (k2_tarski @ X12 @ X14))))),
% 0.58/0.77      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X4 @ X3)
% 0.58/0.77          | ~ (r2_hidden @ X4 @ X2)
% 0.58/0.77          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.77          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X3 @ X0)
% 0.58/0.77          | (r2_hidden @ X1 @ X0)
% 0.58/0.77          | (r2_hidden @ X2 @ X0)
% 0.58/0.77          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '12'])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ sk_B @ X0)
% 0.58/0.77          | (r2_hidden @ sk_C @ X0)
% 0.58/0.77          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '13'])).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.77        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '14'])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.77          | (r2_hidden @ X0 @ X2)
% 0.58/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.77          | (r2_hidden @ sk_C @ X0)
% 0.58/0.77          | (r2_hidden @ sk_C @ 
% 0.58/0.77             (k4_xboole_0 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i]:
% 0.58/0.77         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.58/0.77        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_B @ X0)
% 0.58/0.78          | (r2_hidden @ sk_C @ X0)
% 0.58/0.78          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['9', '13'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      (((r2_hidden @ sk_C @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.78          | (r2_hidden @ X0 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C))
% 0.58/0.78          | (r2_hidden @ sk_C @ X0)
% 0.58/0.78          | (r2_hidden @ sk_C @ (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]:
% 0.58/0.78         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.78          | (r2_hidden @ X0 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.58/0.78          | (r2_hidden @ sk_B @ X0)
% 0.58/0.78          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]:
% 0.58/0.78         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.58/0.78        | (r2_hidden @ sk_C @ (k1_tarski @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['8', '14'])).
% 0.58/0.78  thf(t69_enumset1, axiom,
% 0.58/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.78  thf('32', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.78         ((r2_hidden @ X12 @ X13)
% 0.58/0.78          | (r2_hidden @ X14 @ X13)
% 0.58/0.78          | ((X13) = (k4_xboole_0 @ X13 @ (k2_tarski @ X12 @ X14))))),
% 0.58/0.78      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.58/0.78          | (r2_hidden @ X0 @ X1)
% 0.58/0.78          | (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ X1)
% 0.58/0.78          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['34'])).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X2 @ X0)
% 0.58/0.78          | (r2_hidden @ X1 @ X0)
% 0.58/0.78          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf('38', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.58/0.78          | ~ (r2_hidden @ sk_C @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '37'])).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.58/0.78        | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.58/0.78         ((r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X18)))
% 0.58/0.78          | ((X15) = (X18))
% 0.58/0.78          | ~ (r2_hidden @ X15 @ X16))),
% 0.58/0.78      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k1_mcart_1 @ sk_A) = (X0))
% 0.58/0.78          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.58/0.78             (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ X0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k1_mcart_1 @ sk_A) = (X0))
% 0.58/0.78          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.58/0.78        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['39', '44'])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 0.58/0.78        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.58/0.78         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.58/0.78      inference('split', [status(esa)], ['46'])).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.78         ((r2_hidden @ (k2_mcart_1 @ X19) @ X21)
% 0.58/0.78          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.78  thf('50', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain,
% 0.58/0.78      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.58/0.78        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))
% 0.58/0.78         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)))),
% 0.58/0.78      inference('split', [status(esa)], ['51'])).
% 0.58/0.78  thf('53', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['50', '52'])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.58/0.78       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.58/0.78      inference('split', [status(esa)], ['46'])).
% 0.58/0.78  thf('55', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.58/0.78  thf('56', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['47', '55'])).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['45', '56'])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.58/0.78          | (r2_hidden @ X0 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.78  thf('59', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.58/0.78          | (r2_hidden @ sk_B @ X0)
% 0.58/0.78          | (r2_hidden @ sk_B @ 
% 0.58/0.78             (k4_xboole_0 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]:
% 0.58/0.78         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.78  thf('61', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.78  thf('62', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))),
% 0.58/0.78      inference('simplify', [status(thm)], ['61'])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.58/0.78         ((r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X18)))
% 0.58/0.78          | ((X15) = (X18))
% 0.58/0.78          | ~ (r2_hidden @ X15 @ X16))),
% 0.58/0.78      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.58/0.78  thf('64', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((sk_B) = (X0))
% 0.58/0.78          | (r2_hidden @ sk_B @ 
% 0.58/0.78             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.78  thf('65', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.78          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      (![X0 : $i]: (((sk_B) = (X0)) | ~ (r2_hidden @ sk_B @ (k1_tarski @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.58/0.78        | ((sk_B) = (k1_mcart_1 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '66'])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.58/0.78         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.58/0.78      inference('split', [status(esa)], ['51'])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.58/0.78       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 0.58/0.78      inference('split', [status(esa)], ['51'])).
% 0.58/0.78  thf('70', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['53', '69'])).
% 0.58/0.78  thf('71', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.58/0.78  thf('72', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['67', '71'])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.58/0.78          | ~ (r2_hidden @ sk_C @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '37'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 0.58/0.78        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.78  thf('75', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k1_mcart_1 @ sk_A) = (X0))
% 0.58/0.78          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.58/0.78        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.78  thf('77', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['47', '55'])).
% 0.58/0.78  thf('78', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      (![X0 : $i]: (((sk_B) = (X0)) | ~ (r2_hidden @ sk_B @ (k1_tarski @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.78  thf('80', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.78  thf('81', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.58/0.78  thf('82', plain, ($false),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
