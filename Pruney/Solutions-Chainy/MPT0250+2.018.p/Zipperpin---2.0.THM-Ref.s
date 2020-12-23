%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e1Izf5tnbp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 177 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  844 (1627 expanded)
%              Number of equality atoms :   46 (  83 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( X25 = X26 )
      | ( X25 = X27 )
      | ( X25 = X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ X34 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('62',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','59','60','61'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('63',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(condensation,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference('sup-',[status(thm)],['50','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e1Izf5tnbp
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 357 iterations in 0.175s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.44/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.64  thf(t70_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      (![X37 : $i, X38 : $i]:
% 0.44/0.64         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.44/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.64  thf(d1_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.64       ( ![E:$i]:
% 0.44/0.64         ( ( r2_hidden @ E @ D ) <=>
% 0.44/0.64           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.64  thf(zf_stmt_1, axiom,
% 0.44/0.64    (![E:$i,C:$i,B:$i,A:$i]:
% 0.44/0.64     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.44/0.64       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_2, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.64       ( ![E:$i]:
% 0.44/0.64         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.44/0.64         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.64          | (r2_hidden @ X29 @ X33)
% 0.44/0.64          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.64         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.44/0.64          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.44/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.64          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.64      inference('sup+', [status(thm)], ['0', '2'])).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.64         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.44/0.64         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.44/0.64      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.64  thf('6', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '5'])).
% 0.44/0.64  thf(t69_enumset1, axiom,
% 0.44/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.65  thf('7', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.65         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.44/0.65          | ((X25) = (X26))
% 0.44/0.65          | ((X25) = (X27))
% 0.44/0.65          | ((X25) = (X28)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.65  thf(t3_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.44/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i]:
% 0.44/0.65         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.44/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X34 @ X33)
% 0.44/0.65          | ~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.44/0.65          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.44/0.65         (~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.44/0.65          | ~ (r2_hidden @ X34 @ (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['12'])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.65          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '13'])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.44/0.65          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '14'])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.44/0.65          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.44/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.44/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.44/0.65          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.44/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ X1)
% 0.44/0.65          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.44/0.65          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.44/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.44/0.65          | ~ (r2_hidden @ X8 @ X9)
% 0.44/0.65          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.44/0.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.44/0.65          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.44/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.65          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.44/0.65          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['22', '25'])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '27'])).
% 0.44/0.65  thf(t83_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i]:
% 0.44/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.44/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ X1)
% 0.44/0.65          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf(d5_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.44/0.65       ( ![D:$i]:
% 0.44/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.44/0.65          | (r2_hidden @ X4 @ X1)
% 0.44/0.65          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.65         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.44/0.65          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['31', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.44/0.65          | ~ (r2_hidden @ X4 @ X2)
% 0.44/0.65          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.65  thf('37', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X2)
% 0.44/0.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.44/0.65          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['35', '37'])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.44/0.65          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['34', '38'])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.44/0.65      inference('simplify', [status(thm)], ['39'])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i]:
% 0.44/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.44/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X2)
% 0.44/0.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X2 @ X0)
% 0.44/0.65          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('condensation', [status(thm)], ['46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.44/0.65          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '47'])).
% 0.44/0.65  thf('49', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.44/0.65          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['7', '48'])).
% 0.44/0.65  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['6', '49'])).
% 0.44/0.65  thf('51', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.65  thf(t45_zfmisc_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.44/0.65       ( r2_hidden @ A @ B ) ))).
% 0.44/0.65  thf(zf_stmt_3, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i]:
% 0.44/0.65        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.44/0.65          ( r2_hidden @ A @ B ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.65  thf(d10_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (![X10 : $i, X12 : $i]:
% 0.44/0.65         (((X10) = (X12))
% 0.44/0.65          | ~ (r1_tarski @ X12 @ X10)
% 0.44/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.44/0.65        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.65  thf(commutativity_k2_tarski, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.44/0.65  thf('55', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i]:
% 0.44/0.65         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.65  thf(l51_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('56', plain,
% 0.44/0.65      (![X46 : $i, X47 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('sup+', [status(thm)], ['55', '56'])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (![X46 : $i, X47 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('59', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.44/0.65  thf(t7_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('60', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.65  thf('61', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.44/0.65  thf('62', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('demod', [status(thm)], ['54', '59', '60', '61'])).
% 0.44/0.65  thf(t70_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.44/0.65            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.44/0.65       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.44/0.65            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.44/0.65  thf('63', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X13 @ X16)
% 0.44/0.65          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.44/0.65  thf('64', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('65', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ sk_B)
% 0.44/0.65          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['51', '64'])).
% 0.44/0.65  thf('66', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('67', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('68', plain,
% 0.44/0.65      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.44/0.65          | ~ (r2_hidden @ X8 @ X9)
% 0.44/0.65          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf('69', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.44/0.65          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.44/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf('70', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.65          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.44/0.65          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['66', '69'])).
% 0.44/0.65  thf('71', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ sk_A @ sk_B) | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['65', '71'])).
% 0.44/0.65  thf('73', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.65  thf('74', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)),
% 0.44/0.65      inference('clc', [status(thm)], ['72', '73'])).
% 0.44/0.65  thf('75', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.65  thf('76', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.65  thf('77', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i]:
% 0.44/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.44/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.44/0.65  thf('78', plain,
% 0.44/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.65  thf('79', plain,
% 0.44/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X2)
% 0.44/0.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.65  thf('80', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.44/0.65  thf('81', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('condensation', [status(thm)], ['80'])).
% 0.44/0.65  thf('82', plain, ($false), inference('sup-', [status(thm)], ['50', '81'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
