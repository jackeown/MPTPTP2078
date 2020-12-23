%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0600+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kNh0tp6RVY

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  530 ( 886 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t204_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t204_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_B @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_E_1 @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_E_1 @ sk_B @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_B @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( sk_E_1 @ sk_B @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','18','41'])).


%------------------------------------------------------------------------------
