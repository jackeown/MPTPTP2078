%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0864+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RLm5YXxS1f

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 161 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  489 (1173 expanded)
%              Number of equality atoms :   99 ( 242 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_B_73_type,type,(
    sk_B_73: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_79_type,type,(
    sk_B_79: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X436: $i,X437: $i,X438: $i] :
      ( ( X437 != X436 )
      | ( r2_hidden @ ( X437 @ X438 ) )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X436: $i] :
      ( r2_hidden @ ( X436 @ ( k1_tarski @ X436 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ ( B @ C ) ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('2',plain,
    ( ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) )
    | ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_B_73 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_B_73 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X3909: $i,X3910: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3909 @ X3910 ) ) )
      = X3909 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_73 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A_14
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( sk_A_14
      = ( k4_tarski @ ( sk_A_14 @ sk_C_93 ) ) )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,
    ( ( sk_A_14
      = ( k4_tarski @ ( sk_A_14 @ sk_C_93 ) ) )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ ( A @ B ) )
        = ( k4_tarski @ ( C @ D ) ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('11',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1287 = X1286 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('12',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_14 )
      = sk_C_93 )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( sk_A_14
      = ( k4_tarski @ ( sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) ) )
   <= ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X436: $i] :
      ( r2_hidden @ ( X436 @ ( k1_tarski @ X436 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('16',plain,
    ( ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( sk_A_14
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('18',plain,
    ( sk_A_14
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('19',plain,(
    ! [X3909: $i,X3911: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3909 @ X3911 ) ) )
      = X3911 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = sk_C_93 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A_14
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_A_14
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ sk_A_14 ) ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ ( B @ A ) )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ ( C @ A ) )
                      | ( r2_hidden @ ( D @ A ) ) )
                    & ( B
                      = ( k4_tarski @ ( C @ D ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X3915: $i,X3916: $i,X3917: $i] :
      ( ( X3915 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( X3916 @ X3915 ) )
      | ( ( sk_B_79 @ X3915 )
       != ( k4_tarski @ ( X3917 @ X3916 ) ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X3915: $i,X3916: $i,X3917: $i] :
      ( ( X3915 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( X3916 @ X3915 ) )
      | ( ( sk_B_79 @ X3915 )
       != ( k4_tarski @ ( X3917 @ X3916 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_79 @ X0 )
         != sk_A_14 )
        | ~ ( r2_hidden @ ( sk_A_14 @ X0 ) )
        | ( X0 = o_0_0_xboole_0 ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( ( k1_tarski @ sk_A_14 )
        = o_0_0_xboole_0 )
      | ( ( sk_B_79 @ ( k1_tarski @ sk_A_14 ) )
       != sk_A_14 ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X3915: $i] :
      ( ( X3915 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_79 @ X3915 @ X3915 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X3915: $i] :
      ( ( X3915 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_79 @ X3915 @ X3915 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = o_0_0_xboole_0 )
      | ( ( sk_B_79 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('37',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B_79 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( ( k1_tarski @ sk_A_14 )
        = o_0_0_xboole_0 )
      | ( sk_A_14 != sk_A_14 ) )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['27','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A_14 )
      = o_0_0_xboole_0 )
   <= ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('43',plain,(
    sk_A_14
 != ( k2_mcart_1 @ sk_A_14 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A_14
      = ( k1_mcart_1 @ sk_A_14 ) )
    | ( sk_A_14
      = ( k2_mcart_1 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,
    ( sk_A_14
    = ( k1_mcart_1 @ sk_A_14 ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) ) ),
    inference(simpl_trail,[status(thm)],['14','45'])).

thf('47',plain,(
    ! [X3915: $i,X3916: $i,X3917: $i] :
      ( ( X3915 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( X3917 @ X3915 ) )
      | ( ( sk_B_79 @ X3915 )
       != ( k4_tarski @ ( X3917 @ X3916 ) ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('48',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('49',plain,(
    ! [X3915: $i,X3916: $i,X3917: $i] :
      ( ( X3915 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( X3917 @ X3915 ) )
      | ( ( sk_B_79 @ X3915 )
       != ( k4_tarski @ ( X3917 @ X3916 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_79 @ X0 )
       != sk_A_14 )
      | ~ ( r2_hidden @ ( sk_A_14 @ X0 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A_14 )
      = o_0_0_xboole_0 )
    | ( ( sk_B_79 @ ( k1_tarski @ sk_A_14 ) )
     != sk_A_14 ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B_79 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_A_14 )
      = o_0_0_xboole_0 )
    | ( sk_A_14 != sk_A_14 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A_14 )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
