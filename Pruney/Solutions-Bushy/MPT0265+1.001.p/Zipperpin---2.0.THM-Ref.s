%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0265+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.157KjSOZdY

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:36 EST 2020

% Result     : Theorem 16.06s
% Output     : Refutation 16.06s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 190 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          : 1207 (2431 expanded)
%              Number of equality atoms :  156 ( 320 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t60_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( ( r2_hidden @ C @ B )
            & ( A != C ) )
          | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
            = ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ( sk_A = sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( X11 = X10 )
      | ( X11 = X7 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = X2 )
      | ( ( k2_tarski @ X2 @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k2_tarski @ X2 @ X1 ) @ X2 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X1 ) @ X0 )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X1 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X1 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('11',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
       != X2 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('14',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X0 )
       != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B )
     != ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) )
     != ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
     != ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ X17 @ X15 )
      | ( X16
       != ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X1 )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = X1 )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
       != X2 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
       != X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
       != X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_A )
     != sk_A ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A = sk_C_1 ) ),
    inference('sup+',[status(thm)],['27','51'])).

thf('53',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
      = ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k1_tarski @ sk_C_1 ) )
   <= ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['26','54'])).

thf('56',plain,(
    sk_A != sk_C_1 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X10 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('61',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('67',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X3 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 )
        = X1 )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 )
        = X2 )
      | ( ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k3_xboole_0 @ X3 @ ( k2_tarski @ X2 @ X1 ) ) @ X2 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ X17 @ X14 )
      | ( X16
       != ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ X17 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) @ X2 )
        = X2 )
      | ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) @ X2 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) @ X2 )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
       != X2 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
       != X0 )
      | ( ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
       != X0 )
      | ( ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k1_tarski @ sk_A ) )
      | ( ( sk_C @ ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) @ sk_A )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) @ X2 )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['59','87'])).


%------------------------------------------------------------------------------
