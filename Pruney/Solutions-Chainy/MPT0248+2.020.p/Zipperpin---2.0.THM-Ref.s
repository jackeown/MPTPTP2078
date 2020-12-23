%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6WLGzODCL

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:20 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 331 expanded)
%              Number of leaves         :   25 (  99 expanded)
%              Depth                    :   22
%              Number of atoms          :  835 (3312 expanded)
%              Number of equality atoms :  125 ( 605 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( X36 = X33 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B_2 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('39',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_2 @ X0 )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('57',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('60',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_2 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_2 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','88'])).

thf('90',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('91',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_C_2
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('94',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['26','28','61','92','93'])).

thf('95',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','94'])).

thf('96',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['22','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['4','96'])).

thf('98',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('99',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['26','28','61'])).

thf('100',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6WLGzODCL
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 1900 iterations in 0.556s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.77/1.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/1.01  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.77/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/1.01  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.77/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.01  thf(t43_zfmisc_1, conjecture,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.77/1.01          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.01          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.01          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.77/1.01        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.77/1.01             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.01             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.77/1.01             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.77/1.01  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t7_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('1', plain,
% 0.77/1.01      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/1.01  thf('2', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.77/1.01      inference('sup+', [status(thm)], ['0', '1'])).
% 0.77/1.01  thf(d10_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/1.01  thf('3', plain,
% 0.77/1.01      (![X16 : $i, X18 : $i]:
% 0.77/1.01         (((X16) = (X18))
% 0.77/1.01          | ~ (r1_tarski @ X18 @ X16)
% 0.77/1.01          | ~ (r1_tarski @ X16 @ X18))),
% 0.77/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.01  thf('4', plain,
% 0.77/1.01      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.77/1.01        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/1.01  thf(t7_xboole_0, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/1.01          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/1.01  thf('5', plain,
% 0.77/1.01      (![X15 : $i]:
% 0.77/1.01         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.01  thf('6', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.77/1.01      inference('sup+', [status(thm)], ['0', '1'])).
% 0.77/1.01  thf(d3_tarski, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( r1_tarski @ A @ B ) <=>
% 0.77/1.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/1.01  thf('7', plain,
% 0.77/1.01      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X5 @ X6)
% 0.77/1.01          | (r2_hidden @ X5 @ X7)
% 0.77/1.01          | ~ (r1_tarski @ X6 @ X7))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('8', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.77/1.01      inference('sup-', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('9', plain,
% 0.77/1.01      ((((sk_B_2) = (k1_xboole_0))
% 0.77/1.01        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['5', '8'])).
% 0.77/1.01  thf(d1_tarski, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.77/1.01       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.77/1.01  thf('10', plain,
% 0.77/1.01      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X36 @ X35)
% 0.77/1.01          | ((X36) = (X33))
% 0.77/1.01          | ((X35) != (k1_tarski @ X33)))),
% 0.77/1.01      inference('cnf', [status(esa)], [d1_tarski])).
% 0.77/1.01  thf('11', plain,
% 0.77/1.01      (![X33 : $i, X36 : $i]:
% 0.77/1.01         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['10'])).
% 0.77/1.01  thf('12', plain,
% 0.77/1.01      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_B_2) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['9', '11'])).
% 0.77/1.01  thf('13', plain,
% 0.77/1.01      (![X15 : $i]:
% 0.77/1.01         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.01  thf('14', plain,
% 0.77/1.01      (((r2_hidden @ sk_A @ sk_B_2)
% 0.77/1.01        | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.01        | ((sk_B_2) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['12', '13'])).
% 0.77/1.01  thf('15', plain,
% 0.77/1.01      ((((sk_B_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_2))),
% 0.77/1.01      inference('simplify', [status(thm)], ['14'])).
% 0.77/1.01  thf('16', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('17', plain,
% 0.77/1.01      (![X33 : $i, X36 : $i]:
% 0.77/1.01         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['10'])).
% 0.77/1.01  thf('18', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.77/1.01          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/1.01  thf('19', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('20', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X0 @ X1)
% 0.77/1.01          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.77/1.01          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.77/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.77/1.01      inference('simplify', [status(thm)], ['20'])).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      ((((sk_B_2) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2))),
% 0.77/1.01      inference('sup-', [status(thm)], ['15', '21'])).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('24', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.77/1.01      inference('split', [status(esa)], ['23'])).
% 0.77/1.01  thf('25', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('26', plain,
% 0.77/1.01      (~ (((sk_B_2) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.77/1.01      inference('split', [status(esa)], ['25'])).
% 0.77/1.01  thf('27', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('28', plain,
% 0.77/1.01      (~ (((sk_B_2) = (k1_tarski @ sk_A))) | 
% 0.77/1.01       ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('split', [status(esa)], ['27'])).
% 0.77/1.01  thf('29', plain,
% 0.77/1.01      (![X15 : $i]:
% 0.77/1.01         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.01  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(commutativity_k2_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/1.01  thf('31', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/1.01  thf('33', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/1.01  thf('34', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.77/1.01      inference('sup+', [status(thm)], ['30', '33'])).
% 0.77/1.01  thf('35', plain,
% 0.77/1.01      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X5 @ X6)
% 0.77/1.01          | (r2_hidden @ X5 @ X7)
% 0.77/1.01          | ~ (r1_tarski @ X6 @ X7))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('36', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.77/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/1.01  thf('37', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0))
% 0.77/1.01        | (r2_hidden @ (sk_B_1 @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['29', '36'])).
% 0.77/1.01  thf('38', plain,
% 0.77/1.01      (![X33 : $i, X36 : $i]:
% 0.77/1.01         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['10'])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_2) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.77/1.01  thf('40', plain,
% 0.77/1.01      (![X15 : $i]:
% 0.77/1.01         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.01  thf('41', plain,
% 0.77/1.01      (((r2_hidden @ sk_A @ sk_C_2)
% 0.77/1.01        | ((sk_C_2) = (k1_xboole_0))
% 0.77/1.01        | ((sk_C_2) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['39', '40'])).
% 0.77/1.01  thf('42', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.77/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.77/1.01  thf('43', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('44', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.77/1.01      inference('sup-', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('45', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((r1_tarski @ sk_B_2 @ X0)
% 0.77/1.01          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['43', '44'])).
% 0.77/1.01  thf('46', plain,
% 0.77/1.01      (![X33 : $i, X36 : $i]:
% 0.77/1.01         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['10'])).
% 0.77/1.01  thf('47', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((r1_tarski @ sk_B_2 @ X0) | ((sk_C @ X0 @ sk_B_2) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/1.01  thf('48', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/1.01  thf('49', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (~ (r2_hidden @ sk_A @ X0)
% 0.77/1.01          | (r1_tarski @ sk_B_2 @ X0)
% 0.77/1.01          | (r1_tarski @ sk_B_2 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['47', '48'])).
% 0.77/1.01  thf('50', plain,
% 0.77/1.01      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['49'])).
% 0.77/1.01  thf('51', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0)) | (r1_tarski @ sk_B_2 @ sk_C_2))),
% 0.77/1.01      inference('sup-', [status(thm)], ['42', '50'])).
% 0.77/1.01  thf(t12_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.77/1.01  thf('52', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.77/1.01  thf('53', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0))
% 0.77/1.01        | ((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_C_2)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/1.01  thf('54', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('55', plain,
% 0.77/1.01      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['53', '54'])).
% 0.77/1.01  thf('56', plain,
% 0.77/1.01      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.77/1.01         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('split', [status(esa)], ['23'])).
% 0.77/1.01  thf('57', plain,
% 0.77/1.01      (((((sk_C_2) != (sk_C_2)) | ((sk_C_2) = (k1_xboole_0))))
% 0.77/1.01         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/1.01  thf('58', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('simplify', [status(thm)], ['57'])).
% 0.77/1.01  thf('59', plain,
% 0.77/1.01      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.77/1.01      inference('split', [status(esa)], ['25'])).
% 0.77/1.01  thf('60', plain,
% 0.77/1.01      ((((sk_C_2) != (sk_C_2)))
% 0.77/1.01         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.77/1.01             ~ (((sk_C_2) = (k1_xboole_0))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/1.01  thf('61', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0))) | (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['60'])).
% 0.77/1.01  thf('62', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('simplify', [status(thm)], ['57'])).
% 0.77/1.01  thf(d1_xboole_0, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.77/1.01  thf('63', plain,
% 0.77/1.01      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.77/1.01      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.01  thf('64', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 0.77/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.01  thf('65', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 0.77/1.01      inference('simplify', [status(thm)], ['64'])).
% 0.77/1.01  thf('66', plain,
% 0.77/1.01      (![X19 : $i, X20 : $i]:
% 0.77/1.01         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.77/1.01  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['65', '66'])).
% 0.77/1.01  thf('68', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/1.01  thf(t46_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.77/1.01  thf('69', plain,
% 0.77/1.01      (![X29 : $i, X30 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30)) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.77/1.01  thf('70', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['68', '69'])).
% 0.77/1.01  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['67', '70'])).
% 0.77/1.01  thf(d5_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.77/1.01       ( ![D:$i]:
% 0.77/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.77/1.01           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.77/1.01  thf('72', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X13 @ X12)
% 0.77/1.01          | ~ (r2_hidden @ X13 @ X11)
% 0.77/1.01          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.77/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.77/1.01  thf('73', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X13 @ X11)
% 0.77/1.01          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['72'])).
% 0.77/1.01  thf('74', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['71', '73'])).
% 0.77/1.01  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.77/1.01      inference('condensation', [status(thm)], ['74'])).
% 0.77/1.01  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/1.01      inference('sup-', [status(thm)], ['63', '75'])).
% 0.77/1.01  thf('77', plain,
% 0.77/1.01      (((v1_xboole_0 @ sk_C_2)) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['62', '76'])).
% 0.77/1.01  thf('78', plain,
% 0.77/1.01      (![X15 : $i]:
% 0.77/1.01         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/1.01  thf('79', plain,
% 0.77/1.01      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.77/1.01      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.01  thf('80', plain,
% 0.77/1.01      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['78', '79'])).
% 0.77/1.01  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['67', '70'])).
% 0.77/1.01  thf(t39_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('82', plain,
% 0.77/1.01      (![X21 : $i, X22 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.77/1.01           = (k2_xboole_0 @ X21 @ X22))),
% 0.77/1.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/1.01  thf('83', plain,
% 0.77/1.01      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['81', '82'])).
% 0.77/1.01  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['65', '66'])).
% 0.77/1.01  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['83', '84'])).
% 0.77/1.01  thf('86', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['80', '85'])).
% 0.77/1.01  thf('87', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('88', plain,
% 0.77/1.01      ((((k1_tarski @ sk_A) = (sk_B_2)) | ~ (v1_xboole_0 @ sk_C_2))),
% 0.77/1.01      inference('sup+', [status(thm)], ['86', '87'])).
% 0.77/1.01  thf('89', plain,
% 0.77/1.01      ((((k1_tarski @ sk_A) = (sk_B_2)))
% 0.77/1.01         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['77', '88'])).
% 0.77/1.01  thf('90', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.77/1.01         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('split', [status(esa)], ['25'])).
% 0.77/1.01  thf('91', plain,
% 0.77/1.01      ((((sk_B_2) != (sk_B_2)))
% 0.77/1.01         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.77/1.01             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['89', '90'])).
% 0.77/1.01  thf('92', plain,
% 0.77/1.01      ((((sk_C_2) = (k1_tarski @ sk_A))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['91'])).
% 0.77/1.01  thf('93', plain,
% 0.77/1.01      (~ (((sk_B_2) = (k1_xboole_0))) | ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('split', [status(esa)], ['23'])).
% 0.77/1.01  thf('94', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)],
% 0.77/1.01                ['26', '28', '61', '92', '93'])).
% 0.77/1.01  thf('95', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['24', '94'])).
% 0.77/1.01  thf('96', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['22', '95'])).
% 0.77/1.01  thf('97', plain, (((k1_tarski @ sk_A) = (sk_B_2))),
% 0.77/1.01      inference('demod', [status(thm)], ['4', '96'])).
% 0.77/1.01  thf('98', plain,
% 0.77/1.01      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.77/1.01         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('split', [status(esa)], ['25'])).
% 0.77/1.01  thf('99', plain, (~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)], ['26', '28', '61'])).
% 0.77/1.01  thf('100', plain, (((sk_B_2) != (k1_tarski @ sk_A))),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.77/1.01  thf('101', plain, ($false),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['97', '100'])).
% 0.77/1.01  
% 0.77/1.01  % SZS output end Refutation
% 0.77/1.01  
% 0.84/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
