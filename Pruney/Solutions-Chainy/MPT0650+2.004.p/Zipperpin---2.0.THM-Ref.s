%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0IQtMQcNab

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  146 (1528 expanded)
%              Number of leaves         :   24 ( 433 expanded)
%              Depth                    :   37
%              Number of atoms          : 1351 (23843 expanded)
%              Number of equality atoms :   89 (1591 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X17 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X17 @ X14 ) @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X12 ) @ X10 )
      | ( X12
       != ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( k1_funct_1 @ X10 @ X9 ) ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( X17
        = ( k1_funct_1 @ X14 @ ( sk_D_2 @ X17 @ X14 ) ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X14 ) )
      | ( X17
        = ( k1_funct_1 @ X14 @ ( sk_D_2 @ X17 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['15','22','23','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k1_funct_1 @ X22 @ ( k1_funct_1 @ X23 @ X24 ) ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( X12
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X12 ) @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k4_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k4_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k4_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ( X11
       != ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ X10 @ X9 )
        = k1_xboole_0 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k1_funct_1 @ X22 @ ( k1_funct_1 @ X23 @ X24 ) ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('65',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('73',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('74',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('75',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('82',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('85',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('87',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','86'])).

thf('88',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('89',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('90',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_A != sk_A )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91','92'])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( sk_D_2 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('113',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('115',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('116',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['113','116','117','118'])).

thf('120',plain,(
    $false ),
    inference(simplify,[status(thm)],['119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0IQtMQcNab
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:28:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 310 iterations in 0.236s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.72  thf(d9_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      (![X20 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X20)
% 0.49/0.72          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.49/0.72          | ~ (v1_funct_1 @ X20)
% 0.49/0.72          | ~ (v1_relat_1 @ X20))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.72  thf(dt_k2_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.49/0.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (![X21 : $i]:
% 0.49/0.72         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 0.49/0.72          | ~ (v1_funct_1 @ X21)
% 0.49/0.72          | ~ (v1_relat_1 @ X21))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['0', '1'])).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['2'])).
% 0.49/0.72  thf(dt_k4_relat_1, axiom,
% 0.49/0.72    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.72  thf(t57_funct_1, conjecture,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.72       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.49/0.72         ( ( ( A ) =
% 0.49/0.72             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.49/0.72           ( ( A ) =
% 0.49/0.72             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i]:
% 0.49/0.72        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.72          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.49/0.72            ( ( ( A ) =
% 0.49/0.72                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.49/0.72              ( ( A ) =
% 0.49/0.72                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.49/0.72  thf('6', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d5_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.49/0.72           ( ![C:$i]:
% 0.49/0.72             ( ( r2_hidden @ C @ B ) <=>
% 0.49/0.72               ( ?[D:$i]:
% 0.49/0.72                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.49/0.72                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.49/0.72         (((X16) != (k2_relat_1 @ X14))
% 0.49/0.72          | (r2_hidden @ (sk_D_2 @ X17 @ X14) @ (k1_relat_1 @ X14))
% 0.49/0.72          | ~ (r2_hidden @ X17 @ X16)
% 0.49/0.72          | ~ (v1_funct_1 @ X14)
% 0.49/0.72          | ~ (v1_relat_1 @ X14))),
% 0.49/0.72      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X14 : $i, X17 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X14)
% 0.49/0.72          | ~ (v1_funct_1 @ X14)
% 0.49/0.72          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X14))
% 0.49/0.72          | (r2_hidden @ (sk_D_2 @ X17 @ X14) @ (k1_relat_1 @ X14)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['7'])).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['6', '8'])).
% 0.49/0.72  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      ((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.49/0.72  thf(d4_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ![B:$i,C:$i]:
% 0.49/0.72         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.49/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.49/0.72               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.72           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.49/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.49/0.72               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X9 @ X12) @ X10)
% 0.49/0.72          | ((X12) != (k1_funct_1 @ X10 @ X9))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X10)
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X9 @ (k1_funct_1 @ X10 @ X9)) @ X10)
% 0.49/0.72          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X10)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['13'])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (((r2_hidden @ 
% 0.49/0.72         (k4_tarski @ (sk_D_2 @ sk_A @ sk_B) @ 
% 0.49/0.72          (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B))) @ 
% 0.49/0.72         sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '14'])).
% 0.49/0.72  thf('16', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.49/0.72         (((X16) != (k2_relat_1 @ X14))
% 0.49/0.72          | ((X17) = (k1_funct_1 @ X14 @ (sk_D_2 @ X17 @ X14)))
% 0.49/0.72          | ~ (r2_hidden @ X17 @ X16)
% 0.49/0.72          | ~ (v1_funct_1 @ X14)
% 0.49/0.72          | ~ (v1_relat_1 @ X14))),
% 0.49/0.72      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (![X14 : $i, X17 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X14)
% 0.49/0.72          | ~ (v1_funct_1 @ X14)
% 0.49/0.72          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X14))
% 0.49/0.72          | ((X17) = (k1_funct_1 @ X14 @ (sk_D_2 @ X17 @ X14))))),
% 0.49/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.49/0.72  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('22', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.72  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '22', '23', '24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.72  thf(d7_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( v1_relat_1 @ B ) =>
% 0.49/0.72           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.49/0.72             ( ![C:$i,D:$i]:
% 0.49/0.72               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.49/0.72                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((X0) != (k4_relat_1 @ X1))
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.49/0.72          | ~ (v1_relat_1 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X1)
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k4_relat_1 @ X1))
% 0.49/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['26', '28'])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['29'])).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72           (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['25', '30'])).
% 0.49/0.72  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72        (k4_relat_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.49/0.72  thf(t20_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ C ) =>
% 0.49/0.72       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.49/0.72         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.49/0.72           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.49/0.72  thf('34', plain,
% 0.49/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.49/0.72         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.49/0.72          | (r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.49/0.72          | ~ (v1_relat_1 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['5', '35'])).
% 0.49/0.72  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('38', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.72  thf(t23_funct_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.72       ( ![C:$i]:
% 0.49/0.72         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.72           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.72             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.49/0.72               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.49/0.72  thf('39', plain,
% 0.49/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X22)
% 0.49/0.72          | ~ (v1_funct_1 @ X22)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 0.49/0.72              = (k1_funct_1 @ X22 @ (k1_funct_1 @ X23 @ X24)))
% 0.49/0.72          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.49/0.72          | ~ (v1_funct_1 @ X23)
% 0.49/0.72          | ~ (v1_relat_1 @ X23))),
% 0.49/0.72      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72        (k4_relat_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['2'])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.72  thf('44', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.49/0.72          | ((X12) = (k1_funct_1 @ X10 @ X9))
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ X9 @ X12) @ X10)
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((X0) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ sk_B)
% 0.49/0.72          | ((X0) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['43', '46'])).
% 0.49/0.72  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((X0) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['47', '48'])).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ sk_B)
% 0.49/0.72          | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72          | ~ (v2_funct_1 @ sk_B)
% 0.49/0.72          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((X0) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['42', '49'])).
% 0.49/0.72  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('53', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((X0) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.49/0.72  thf('55', plain,
% 0.49/0.72      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '54'])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['40', '55'])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['2'])).
% 0.49/0.72  thf('58', plain,
% 0.49/0.72      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.72         ((r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.49/0.72          | ((X11) = (k1_xboole_0))
% 0.49/0.72          | ((X11) != (k1_funct_1 @ X10 @ X9))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X10)
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ((k1_funct_1 @ X10 @ X9) = (k1_xboole_0))
% 0.49/0.72          | (r2_hidden @ X9 @ (k1_relat_1 @ X10)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['59'])).
% 0.49/0.72  thf('61', plain,
% 0.49/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X22)
% 0.49/0.72          | ~ (v1_funct_1 @ X22)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 0.49/0.72              = (k1_funct_1 @ X22 @ (k1_funct_1 @ X23 @ X24)))
% 0.49/0.72          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.49/0.72          | ~ (v1_funct_1 @ X23)
% 0.49/0.72          | ~ (v1_relat_1 @ X23))),
% 0.49/0.72      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ X1)
% 0.49/0.72              = (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1)))
% 0.49/0.72          | ~ (v1_funct_1 @ X2)
% 0.49/0.72          | ~ (v1_relat_1 @ X2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X2)
% 0.49/0.72          | ~ (v1_funct_1 @ X2)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ X1)
% 0.49/0.72              = (k1_funct_1 @ X2 @ (k1_funct_1 @ X0 @ X1)))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['62'])).
% 0.49/0.72  thf('64', plain,
% 0.49/0.72      (![X20 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X20)
% 0.49/0.72          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.49/0.72          | ~ (v1_funct_1 @ X20)
% 0.49/0.72          | ~ (v1_relat_1 @ X20))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.49/0.72        | ((sk_A)
% 0.49/0.72            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('66', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.49/0.72                   sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['65'])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (((((sk_A)
% 0.49/0.72           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.49/0.72         | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72         | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72         | ~ (v2_funct_1 @ sk_B)))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.49/0.72                   sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['64', '66'])).
% 0.49/0.72  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('70', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('71', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.49/0.72                   sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.49/0.72  thf('72', plain,
% 0.49/0.72      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '54'])).
% 0.49/0.72  thf('73', plain,
% 0.49/0.72      (![X20 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X20)
% 0.49/0.72          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.49/0.72          | ~ (v1_funct_1 @ X20)
% 0.49/0.72          | ~ (v1_relat_1 @ X20))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.72  thf('74', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ sk_B @ 
% 0.49/0.72                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.49/0.72      inference('split', [status(esa)], ['65'])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      (((((sk_A)
% 0.49/0.72           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.49/0.72         | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72         | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72         | ~ (v2_funct_1 @ sk_B)))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ sk_B @ 
% 0.49/0.72                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['73', '74'])).
% 0.49/0.72  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('78', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('79', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ sk_B @ 
% 0.49/0.72                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B))))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ sk_B @ 
% 0.49/0.72                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['72', '79'])).
% 0.49/0.72  thf('81', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      ((((sk_A) != (sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             (((sk_A)
% 0.49/0.72                = (k1_funct_1 @ sk_B @ 
% 0.49/0.72                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['80', '81'])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.49/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      (~
% 0.49/0.72       (((sk_A)
% 0.49/0.72          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.49/0.72       ~
% 0.49/0.72       (((sk_A)
% 0.49/0.72          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['65'])).
% 0.49/0.72  thf('85', plain,
% 0.49/0.72      (~
% 0.49/0.72       (((sk_A)
% 0.49/0.72          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      (((sk_A)
% 0.49/0.72         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 0.49/0.72  thf('87', plain,
% 0.49/0.72      ((((sk_A)
% 0.49/0.72          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.49/0.72        | ((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['63', '86'])).
% 0.49/0.72  thf('88', plain,
% 0.49/0.72      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '54'])).
% 0.49/0.72  thf('89', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.72  thf('90', plain,
% 0.49/0.72      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '54'])).
% 0.49/0.72  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('93', plain,
% 0.49/0.72      ((((sk_A) != (sk_A))
% 0.49/0.72        | ((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['87', '88', '89', '90', '91', '92'])).
% 0.49/0.72  thf('94', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72        | ((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['93'])).
% 0.49/0.72  thf('95', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['58', '94'])).
% 0.49/0.72  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('97', plain,
% 0.49/0.72      ((((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['95', '96'])).
% 0.49/0.72  thf('98', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.72        | ((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['57', '97'])).
% 0.49/0.72  thf('99', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('101', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('102', plain, (((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.49/0.72  thf('103', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['56', '102'])).
% 0.49/0.72  thf('104', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ sk_B)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['4', '103'])).
% 0.49/0.72  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('106', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['104', '105'])).
% 0.49/0.72  thf('107', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ sk_B)
% 0.49/0.72          | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72          | ~ (v2_funct_1 @ sk_B)
% 0.49/0.72          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72              = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['3', '106'])).
% 0.49/0.72  thf('108', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('110', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('111', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.49/0.72            = (k1_funct_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.49/0.72  thf('112', plain,
% 0.49/0.72      (((sk_A)
% 0.49/0.72         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 0.49/0.72  thf('113', plain,
% 0.49/0.72      ((((sk_A) != (k1_funct_1 @ sk_B @ k1_xboole_0))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.72  thf('114', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.72  thf('115', plain, (((sk_D_2 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.49/0.72  thf('116', plain, (((sk_A) = (k1_funct_1 @ sk_B @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['114', '115'])).
% 0.49/0.72  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('119', plain, (((sk_A) != (sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['113', '116', '117', '118'])).
% 0.49/0.72  thf('120', plain, ($false), inference('simplify', [status(thm)], ['119'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
