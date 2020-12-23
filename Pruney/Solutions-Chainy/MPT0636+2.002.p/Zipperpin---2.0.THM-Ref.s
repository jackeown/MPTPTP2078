%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3EyyW8iyQQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 212 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          : 1084 (2923 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t40_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('4',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('16',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t75_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
      <=> ( ( r2_hidden @ B @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,
    ( ( ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('51',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X5 ) ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X5 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t75_relat_1])).

thf('70',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('74',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A )
        = ( k1_funct_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['67','77'])).

thf('79',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('80',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','45','46','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3EyyW8iyQQ
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 119 iterations in 0.093s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(t40_funct_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55       ( ( r2_hidden @
% 0.20/0.55           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.20/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.55           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55          ( ( r2_hidden @
% 0.20/0.55              A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.20/0.55            ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.55              ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t40_funct_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_A @ 
% 0.20/0.55           (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.55       ((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf(t21_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.55             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.55               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X12)
% 0.20/0.55          | ~ (v1_funct_1 @ X12)
% 0.20/0.55          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X14)))
% 0.20/0.55          | (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.20/0.55          | ~ (v1_funct_1 @ X14)
% 0.20/0.55          | ~ (v1_relat_1 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(fc3_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('5', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('6', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.55        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (r2_hidden @ sk_A @ 
% 0.20/0.55             (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.55       ~
% 0.20/0.55       ((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.55       ~
% 0.20/0.55       ((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))) | 
% 0.20/0.55       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf(fc2_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.20/0.55         ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.20/0.55         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | (v1_funct_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.55        | (r2_hidden @ sk_A @ 
% 0.20/0.55           (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.55         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf(t8_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.55          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ X16)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.20/0.55          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.55  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.55  thf(t75_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ D ) =>
% 0.20/0.55       ( ( r2_hidden @
% 0.20/0.55           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.20/0.55         ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.55          | ~ (r2_hidden @ (k4_tarski @ X6 @ X4) @ X7)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X6 @ X4) @ 
% 0.20/0.55             (k5_relat_1 @ X7 @ (k6_relat_1 @ X5)))
% 0.20/0.55          | ~ (v1_relat_1 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (~ (v1_relat_1 @ sk_C)
% 0.20/0.55           | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.55              (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))
% 0.20/0.55           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.55            (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))
% 0.20/0.55           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.55         (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.55          | (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.55          | ~ (v1_funct_1 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | (r2_hidden @ sk_A @ 
% 0.20/0.55            (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | (r2_hidden @ sk_A @ 
% 0.20/0.55            (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))
% 0.20/0.55         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '31'])).
% 0.20/0.55  thf('33', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('34', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((r2_hidden @ sk_A @ 
% 0.20/0.55          (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))
% 0.20/0.55         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | (r2_hidden @ sk_A @ 
% 0.20/0.55            (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '37'])).
% 0.20/0.55  thf('39', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('40', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ 
% 0.20/0.55           (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.55       ((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))) | 
% 0.20/0.55       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))) | 
% 0.20/0.55       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.55      inference('split', [status(esa)], ['16'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | (v1_funct_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ X16)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.20/0.55          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      ((((r2_hidden @ 
% 0.20/0.55          (k4_tarski @ sk_A @ 
% 0.20/0.55           (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55          (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | (r2_hidden @ 
% 0.20/0.55            (k4_tarski @ sk_A @ 
% 0.20/0.55             (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55            (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.55  thf('53', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('54', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.20/0.55         | (r2_hidden @ 
% 0.20/0.55            (k4_tarski @ sk_A @ 
% 0.20/0.55             (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55            (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (((~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | (r2_hidden @ 
% 0.20/0.55            (k4_tarski @ sk_A @ 
% 0.20/0.55             (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55            (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '57'])).
% 0.20/0.55  thf('59', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('60', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (((r2_hidden @ 
% 0.20/0.55         (k4_tarski @ sk_A @ 
% 0.20/0.55          (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55         (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X6 @ X4) @ 
% 0.20/0.55             (k5_relat_1 @ X7 @ (k6_relat_1 @ X5)))
% 0.20/0.55          | (r2_hidden @ X4 @ X5)
% 0.20/0.55          | ~ (v1_relat_1 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | (r2_hidden @ 
% 0.20/0.55            (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A) @ 
% 0.20/0.55            sk_B)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (((r2_hidden @ 
% 0.20/0.55         (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A) @ sk_B))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (((r2_hidden @ 
% 0.20/0.55         (k4_tarski @ sk_A @ 
% 0.20/0.55          (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55         (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X6 @ X4) @ 
% 0.20/0.55             (k5_relat_1 @ X7 @ (k6_relat_1 @ X5)))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X6 @ X4) @ X7)
% 0.20/0.55          | ~ (v1_relat_1 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t75_relat_1])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | (r2_hidden @ 
% 0.20/0.55            (k4_tarski @ sk_A @ 
% 0.20/0.55             (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55            sk_C)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.55  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (((r2_hidden @ 
% 0.20/0.55         (k4_tarski @ sk_A @ 
% 0.20/0.55          (k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)) @ 
% 0.20/0.55         sk_C))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.55          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.20/0.55          | ~ (v1_funct_1 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | ((k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.55             = (k1_funct_1 @ sk_C @ sk_A))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.55  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.55          = (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))))),
% 0.20/0.55      inference('demod', [status(thm)], ['67', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.55         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (~
% 0.20/0.55       ((r2_hidden @ sk_A @ 
% 0.20/0.55         (k1_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B))))) | 
% 0.20/0.55       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.55  thf('81', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)],
% 0.20/0.55                ['1', '12', '13', '45', '46', '80'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
