%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TTWVFhlRwd

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 355 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          :  958 (3864 expanded)
%              Number of equality atoms :  112 ( 696 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( r1_xboole_0 @ X14 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('14',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['13'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    r1_xboole_0 @ sk_B_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('41',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('44',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('51',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['40','42','52'])).

thf('54',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['39','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['30','55'])).

thf('57',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('59',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X59: $i,X61: $i,X62: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X59 @ X61 ) @ X62 )
      | ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r2_hidden @ X59 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('65',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('82',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','22'])).

thf('84',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('86',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('88',plain,(
    r1_xboole_0 @ sk_C_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['39','53'])).

thf('95',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('97',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X15 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('104',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('106',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','22'])).

thf('108',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','54'])).

thf('110',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('112',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['105','112'])).

thf('114',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['56','114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TTWVFhlRwd
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.28/2.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.28/2.47  % Solved by: fo/fo7.sh
% 2.28/2.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.28/2.47  % done 5517 iterations in 2.016s
% 2.28/2.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.28/2.47  % SZS output start Refutation
% 2.28/2.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.28/2.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.28/2.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.28/2.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.28/2.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.28/2.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.28/2.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.28/2.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.28/2.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.28/2.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.28/2.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.28/2.47  thf(sk_A_type, type, sk_A: $i).
% 2.28/2.47  thf(l27_zfmisc_1, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.28/2.47  thf('0', plain,
% 2.28/2.47      (![X52 : $i, X53 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ (k1_tarski @ X52) @ X53) | (r2_hidden @ X52 @ X53))),
% 2.28/2.47      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.28/2.47  thf(symmetry_r1_xboole_0, axiom,
% 2.28/2.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.28/2.47  thf('1', plain,
% 2.28/2.47      (![X7 : $i, X8 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 2.28/2.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.28/2.47  thf('2', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]:
% 2.28/2.47         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['0', '1'])).
% 2.28/2.47  thf(t43_zfmisc_1, conjecture,
% 2.28/2.47    (![A:$i,B:$i,C:$i]:
% 2.28/2.47     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.28/2.47          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.28/2.47          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.28/2.47          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.28/2.47  thf(zf_stmt_0, negated_conjecture,
% 2.28/2.47    (~( ![A:$i,B:$i,C:$i]:
% 2.28/2.47        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.28/2.47             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.28/2.47             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.28/2.47             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 2.28/2.47    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 2.28/2.47  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf(t7_xboole_1, axiom,
% 2.28/2.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.28/2.47  thf('4', plain,
% 2.28/2.47      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.28/2.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.28/2.47  thf('5', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 2.28/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.28/2.47  thf(t12_xboole_1, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.28/2.47  thf('6', plain,
% 2.28/2.47      (![X12 : $i, X13 : $i]:
% 2.28/2.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 2.28/2.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.28/2.47  thf('7', plain,
% 2.28/2.47      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 2.28/2.47      inference('sup-', [status(thm)], ['5', '6'])).
% 2.28/2.47  thf(t70_xboole_1, axiom,
% 2.28/2.47    (![A:$i,B:$i,C:$i]:
% 2.28/2.47     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.28/2.47            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.28/2.47       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.28/2.47            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.28/2.47  thf('8', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ X19)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('9', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 2.28/2.47          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['7', '8'])).
% 2.28/2.47  thf('10', plain,
% 2.28/2.47      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['2', '9'])).
% 2.28/2.47  thf(d1_xboole_0, axiom,
% 2.28/2.47    (![A:$i]:
% 2.28/2.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.28/2.47  thf('11', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.28/2.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.28/2.47  thf('12', plain,
% 2.28/2.47      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['10', '11'])).
% 2.28/2.47  thf(t66_xboole_1, axiom,
% 2.28/2.47    (![A:$i]:
% 2.28/2.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 2.28/2.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 2.28/2.47  thf('13', plain,
% 2.28/2.47      (![X14 : $i]: ((r1_xboole_0 @ X14 @ X14) | ((X14) != (k1_xboole_0)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t66_xboole_1])).
% 2.28/2.47  thf('14', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.28/2.47      inference('simplify', [status(thm)], ['13'])).
% 2.28/2.47  thf('15', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ X19)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ X20))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('16', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 2.28/2.47          | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['14', '15'])).
% 2.28/2.47  thf('17', plain,
% 2.28/2.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.28/2.47        | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B_1)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['12', '16'])).
% 2.28/2.47  thf('18', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.28/2.47      inference('simplify', [status(thm)], ['13'])).
% 2.28/2.47  thf(t69_xboole_1, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.28/2.47       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.28/2.47  thf('19', plain,
% 2.28/2.47      (![X16 : $i, X17 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X16 @ X17)
% 2.28/2.47          | ~ (r1_tarski @ X16 @ X17)
% 2.28/2.47          | (v1_xboole_0 @ X16))),
% 2.28/2.47      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.28/2.47  thf('20', plain,
% 2.28/2.47      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['18', '19'])).
% 2.28/2.47  thf(d10_xboole_0, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.28/2.47  thf('21', plain,
% 2.28/2.47      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 2.28/2.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.28/2.47  thf('22', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 2.28/2.47      inference('simplify', [status(thm)], ['21'])).
% 2.28/2.47  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.28/2.47      inference('demod', [status(thm)], ['20', '22'])).
% 2.28/2.47  thf('24', plain,
% 2.28/2.47      ((r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B_1))),
% 2.28/2.47      inference('demod', [status(thm)], ['17', '23'])).
% 2.28/2.47  thf('25', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ X21)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B_1)),
% 2.28/2.47      inference('sup-', [status(thm)], ['24', '25'])).
% 2.28/2.47  thf('27', plain,
% 2.28/2.47      (![X7 : $i, X8 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 2.28/2.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.28/2.47  thf('28', plain, ((r1_xboole_0 @ sk_B_1 @ k1_xboole_0)),
% 2.28/2.47      inference('sup-', [status(thm)], ['26', '27'])).
% 2.28/2.47  thf('29', plain,
% 2.28/2.47      (![X16 : $i, X17 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X16 @ X17)
% 2.28/2.47          | ~ (r1_tarski @ X16 @ X17)
% 2.28/2.47          | (v1_xboole_0 @ X16))),
% 2.28/2.47      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.28/2.47  thf('30', plain,
% 2.28/2.47      (((v1_xboole_0 @ sk_B_1) | ~ (r1_tarski @ sk_B_1 @ k1_xboole_0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['28', '29'])).
% 2.28/2.47  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf(d3_tarski, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( r1_tarski @ A @ B ) <=>
% 2.28/2.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.28/2.47  thf('32', plain,
% 2.28/2.47      (![X4 : $i, X6 : $i]:
% 2.28/2.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.28/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.28/2.47  thf('33', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.28/2.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.28/2.47  thf('34', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['32', '33'])).
% 2.28/2.47  thf('35', plain,
% 2.28/2.47      (![X12 : $i, X13 : $i]:
% 2.28/2.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 2.28/2.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.28/2.47  thf('36', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]:
% 2.28/2.47         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['34', '35'])).
% 2.28/2.47  thf('37', plain,
% 2.28/2.47      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.28/2.47      inference('sup+', [status(thm)], ['31', '36'])).
% 2.28/2.47  thf('38', plain,
% 2.28/2.47      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf('39', plain,
% 2.28/2.47      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 2.28/2.47         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('split', [status(esa)], ['38'])).
% 2.28/2.47  thf('40', plain,
% 2.28/2.47      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('split', [status(esa)], ['38'])).
% 2.28/2.47  thf('41', plain,
% 2.28/2.47      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf('42', plain,
% 2.28/2.47      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 2.28/2.47       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('split', [status(esa)], ['41'])).
% 2.28/2.47  thf('43', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 2.28/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.28/2.47  thf(l3_zfmisc_1, axiom,
% 2.28/2.47    (![A:$i,B:$i]:
% 2.28/2.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.28/2.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.28/2.47  thf('44', plain,
% 2.28/2.47      (![X54 : $i, X55 : $i]:
% 2.28/2.47         (((X55) = (k1_tarski @ X54))
% 2.28/2.47          | ((X55) = (k1_xboole_0))
% 2.28/2.47          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 2.28/2.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.28/2.47  thf('45', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['43', '44'])).
% 2.28/2.47  thf('46', plain,
% 2.28/2.47      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf('47', plain,
% 2.28/2.47      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 2.28/2.47         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('split', [status(esa)], ['46'])).
% 2.28/2.47  thf('48', plain,
% 2.28/2.47      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 2.28/2.47         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('sup-', [status(thm)], ['45', '47'])).
% 2.28/2.47  thf('49', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('simplify', [status(thm)], ['48'])).
% 2.28/2.47  thf('50', plain,
% 2.28/2.47      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.28/2.47      inference('split', [status(esa)], ['38'])).
% 2.28/2.47  thf('51', plain,
% 2.28/2.47      ((((sk_B_1) != (sk_B_1)))
% 2.28/2.47         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.28/2.47             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('sup-', [status(thm)], ['49', '50'])).
% 2.28/2.47  thf('52', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('simplify', [status(thm)], ['51'])).
% 2.28/2.47  thf('53', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sat_resolution*', [status(thm)], ['40', '42', '52'])).
% 2.28/2.47  thf('54', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 2.28/2.47      inference('simpl_trail', [status(thm)], ['39', '53'])).
% 2.28/2.47  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.28/2.47      inference('simplify_reflect-', [status(thm)], ['37', '54'])).
% 2.28/2.47  thf('56', plain, (~ (r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 2.28/2.47      inference('clc', [status(thm)], ['30', '55'])).
% 2.28/2.47  thf('57', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['43', '44'])).
% 2.28/2.47  thf('58', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['43', '44'])).
% 2.28/2.47  thf('59', plain,
% 2.28/2.47      (![X52 : $i, X53 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ (k1_tarski @ X52) @ X53) | (r2_hidden @ X52 @ X53))),
% 2.28/2.47      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.28/2.47  thf('60', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r2_hidden @ sk_A @ X0))),
% 2.28/2.47      inference('sup+', [status(thm)], ['58', '59'])).
% 2.28/2.47  thf('61', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r2_hidden @ sk_A @ X0))),
% 2.28/2.47      inference('sup+', [status(thm)], ['58', '59'])).
% 2.28/2.47  thf(t38_zfmisc_1, axiom,
% 2.28/2.47    (![A:$i,B:$i,C:$i]:
% 2.28/2.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 2.28/2.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 2.28/2.47  thf('62', plain,
% 2.28/2.47      (![X59 : $i, X61 : $i, X62 : $i]:
% 2.28/2.47         ((r1_tarski @ (k2_tarski @ X59 @ X61) @ X62)
% 2.28/2.47          | ~ (r2_hidden @ X61 @ X62)
% 2.28/2.47          | ~ (r2_hidden @ X59 @ X62))),
% 2.28/2.47      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.28/2.47  thf('63', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]:
% 2.28/2.47         (((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ~ (r2_hidden @ X1 @ X0)
% 2.28/2.47          | (r1_tarski @ (k2_tarski @ X1 @ sk_A) @ X0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['61', '62'])).
% 2.28/2.47  thf('64', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ X0)
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['60', '63'])).
% 2.28/2.47  thf(t69_enumset1, axiom,
% 2.28/2.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.28/2.47  thf('65', plain,
% 2.28/2.47      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 2.28/2.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.28/2.47  thf('66', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('demod', [status(thm)], ['64', '65'])).
% 2.28/2.47  thf('67', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('simplify', [status(thm)], ['66'])).
% 2.28/2.47  thf('68', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         ((r1_tarski @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0))),
% 2.28/2.47      inference('sup+', [status(thm)], ['57', '67'])).
% 2.28/2.47  thf('69', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_tarski @ sk_B_1 @ X0))),
% 2.28/2.47      inference('simplify', [status(thm)], ['68'])).
% 2.28/2.47  thf('70', plain,
% 2.28/2.47      (![X12 : $i, X13 : $i]:
% 2.28/2.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 2.28/2.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.28/2.47  thf('71', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ sk_B_1 @ X0)
% 2.28/2.47          | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['69', '70'])).
% 2.28/2.47  thf('72', plain,
% 2.28/2.47      (![X7 : $i, X8 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 2.28/2.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.28/2.47  thf('73', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (((k2_xboole_0 @ sk_B_1 @ X0) = (X0))
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['71', '72'])).
% 2.28/2.47  thf('74', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]:
% 2.28/2.47         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['0', '1'])).
% 2.28/2.47  thf('75', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf('76', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ X21)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('77', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 2.28/2.47          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['75', '76'])).
% 2.28/2.47  thf('78', plain,
% 2.28/2.47      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['74', '77'])).
% 2.28/2.47  thf('79', plain,
% 2.28/2.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.28/2.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.28/2.47  thf('80', plain,
% 2.28/2.47      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_1) | ~ (v1_xboole_0 @ X0))),
% 2.28/2.47      inference('sup-', [status(thm)], ['78', '79'])).
% 2.28/2.47  thf('81', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 2.28/2.47          | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['14', '15'])).
% 2.28/2.47  thf('82', plain,
% 2.28/2.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.28/2.47        | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_C_1)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['80', '81'])).
% 2.28/2.47  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.28/2.47      inference('demod', [status(thm)], ['20', '22'])).
% 2.28/2.47  thf('84', plain,
% 2.28/2.47      ((r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_C_1))),
% 2.28/2.47      inference('demod', [status(thm)], ['82', '83'])).
% 2.28/2.47  thf('85', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ X21)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('86', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_C_1)),
% 2.28/2.47      inference('sup-', [status(thm)], ['84', '85'])).
% 2.28/2.47  thf('87', plain,
% 2.28/2.47      (![X7 : $i, X8 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 2.28/2.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.28/2.47  thf('88', plain, ((r1_xboole_0 @ sk_C_1 @ k1_xboole_0)),
% 2.28/2.47      inference('sup-', [status(thm)], ['86', '87'])).
% 2.28/2.47  thf('89', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ X19)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ X20))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('90', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 2.28/2.47          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['88', '89'])).
% 2.28/2.47  thf('91', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))
% 2.28/2.47        | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 2.28/2.47        | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B_1)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['73', '90'])).
% 2.28/2.47  thf('92', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.28/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.47  thf('93', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))
% 2.28/2.47        | ((k1_tarski @ sk_A) = (sk_C_1))
% 2.28/2.47        | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B_1)))),
% 2.28/2.47      inference('demod', [status(thm)], ['91', '92'])).
% 2.28/2.47  thf('94', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 2.28/2.47      inference('simpl_trail', [status(thm)], ['39', '53'])).
% 2.28/2.47  thf('95', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))
% 2.28/2.47        | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B_1)))),
% 2.28/2.47      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 2.28/2.47  thf('96', plain,
% 2.28/2.47      (![X18 : $i, X19 : $i, X21 : $i]:
% 2.28/2.47         ((r1_xboole_0 @ X18 @ X21)
% 2.28/2.47          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 2.28/2.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.28/2.47  thf('97', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | (r1_xboole_0 @ sk_C_1 @ sk_B_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['95', '96'])).
% 2.28/2.47  thf('98', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['43', '44'])).
% 2.28/2.47  thf('99', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 2.28/2.47          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['75', '76'])).
% 2.28/2.47  thf('100', plain,
% 2.28/2.47      (![X0 : $i]:
% 2.28/2.47         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 2.28/2.47          | ((sk_B_1) = (k1_xboole_0))
% 2.28/2.47          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.28/2.47      inference('sup-', [status(thm)], ['98', '99'])).
% 2.28/2.47  thf('101', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))
% 2.28/2.47        | (r1_xboole_0 @ sk_C_1 @ sk_C_1)
% 2.28/2.47        | ((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['97', '100'])).
% 2.28/2.47  thf('102', plain,
% 2.28/2.47      (((r1_xboole_0 @ sk_C_1 @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('simplify', [status(thm)], ['101'])).
% 2.28/2.47  thf('103', plain,
% 2.28/2.47      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X15 @ X15))),
% 2.28/2.47      inference('cnf', [status(esa)], [t66_xboole_1])).
% 2.28/2.47  thf('104', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['102', '103'])).
% 2.28/2.47  thf('105', plain,
% 2.28/2.47      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 2.28/2.47      inference('split', [status(esa)], ['46'])).
% 2.28/2.47  thf('106', plain,
% 2.28/2.47      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('simplify', [status(thm)], ['48'])).
% 2.28/2.47  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.28/2.47      inference('demod', [status(thm)], ['20', '22'])).
% 2.28/2.47  thf('108', plain,
% 2.28/2.47      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.28/2.47      inference('sup+', [status(thm)], ['106', '107'])).
% 2.28/2.47  thf('109', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.28/2.47      inference('simplify_reflect-', [status(thm)], ['37', '54'])).
% 2.28/2.47  thf('110', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('sup-', [status(thm)], ['108', '109'])).
% 2.28/2.47  thf('111', plain,
% 2.28/2.47      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.28/2.47      inference('split', [status(esa)], ['46'])).
% 2.28/2.47  thf('112', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 2.28/2.47      inference('sat_resolution*', [status(thm)], ['110', '111'])).
% 2.28/2.47  thf('113', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.28/2.47      inference('simpl_trail', [status(thm)], ['105', '112'])).
% 2.28/2.47  thf('114', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.28/2.47      inference('simplify_reflect-', [status(thm)], ['104', '113'])).
% 2.28/2.47  thf('115', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 2.28/2.47      inference('simplify', [status(thm)], ['21'])).
% 2.28/2.47  thf('116', plain, ($false),
% 2.28/2.47      inference('demod', [status(thm)], ['56', '114', '115'])).
% 2.28/2.47  
% 2.28/2.47  % SZS output end Refutation
% 2.28/2.47  
% 2.28/2.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
