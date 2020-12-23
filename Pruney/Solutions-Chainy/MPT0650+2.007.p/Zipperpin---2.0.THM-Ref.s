%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e10EZB1AtV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 339 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   21
%              Number of atoms          : 1038 (5090 expanded)
%              Number of equality atoms :   62 ( 345 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_2 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( sk_D_2 @ X13 @ X10 ) @ ( k1_relat_1 @ X10 ) ) ) ),
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

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( X23
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_2 @ X13 @ X10 ) ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X10 ) )
      | ( X13
        = ( k1_funct_1 @ X10 @ ( sk_D_2 @ X13 @ X10 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k1_funct_1 @ X18 @ ( k1_funct_1 @ X19 @ X20 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( sk_D_2 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( sk_D_2 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('64',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( sk_D_2 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('72',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('74',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('81',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('84',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','84'])).

thf('86',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','85'])).

thf('87',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e10EZB1AtV
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:52:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 139 iterations in 0.161s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.40/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(d9_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X16 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X16)
% 0.40/0.62          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.40/0.62          | ~ (v1_funct_1 @ X16)
% 0.40/0.62          | ~ (v1_relat_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.40/0.62  thf(dt_k2_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X17 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 0.40/0.62          | ~ (v1_funct_1 @ X17)
% 0.40/0.62          | ~ (v1_relat_1 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['0', '1'])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.40/0.62  thf(dt_k4_relat_1, axiom,
% 0.40/0.62    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.62  thf(t57_funct_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.40/0.62         ( ( ( A ) =
% 0.40/0.62             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.40/0.62           ( ( A ) =
% 0.40/0.62             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.40/0.62            ( ( ( A ) =
% 0.40/0.62                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.40/0.62              ( ( A ) =
% 0.40/0.62                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.40/0.62  thf('6', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d5_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.62               ( ?[D:$i]:
% 0.40/0.62                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.40/0.62                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (((X12) != (k2_relat_1 @ X10))
% 0.40/0.62          | (r2_hidden @ (sk_D_2 @ X13 @ X10) @ (k1_relat_1 @ X10))
% 0.40/0.62          | ~ (r2_hidden @ X13 @ X12)
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X10 : $i, X13 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X10)
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.40/0.62          | (r2_hidden @ (sk_D_2 @ X13 @ X10) @ (k1_relat_1 @ X10)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '8'])).
% 0.40/0.62  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      ((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.40/0.62  thf(t8_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.40/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.40/0.62          | ((X23) != (k1_funct_1 @ X22 @ X21))
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.40/0.62          | ~ (v1_funct_1 @ X22)
% 0.40/0.62          | ~ (v1_relat_1 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X22)
% 0.40/0.62          | ~ (v1_funct_1 @ X22)
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 0.40/0.62          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (((r2_hidden @ 
% 0.40/0.62         (k4_tarski @ (sk_D_2 @ sk_A @ sk_B) @ 
% 0.40/0.62          (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B))) @ 
% 0.40/0.62         sk_B)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.40/0.62  thf('16', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (((X12) != (k2_relat_1 @ X10))
% 0.40/0.62          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_2 @ X13 @ X10)))
% 0.40/0.62          | ~ (r2_hidden @ X13 @ X12)
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X10 : $i, X13 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X10)
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X10))
% 0.40/0.62          | ((X13) = (k1_funct_1 @ X10 @ (sk_D_2 @ X13 @ X10))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['16', '18'])).
% 0.40/0.62  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('22', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.40/0.62  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '22', '23', '24'])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.62  thf(d7_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( v1_relat_1 @ B ) =>
% 0.40/0.62           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.40/0.62             ( ![C:$i,D:$i]:
% 0.40/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.40/0.62                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((X0) != (k4_relat_1 @ X1))
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.40/0.62          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k4_relat_1 @ X1))
% 0.40/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.40/0.62          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.40/0.62           (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '30'])).
% 0.40/0.62  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.40/0.62        (k4_relat_1 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf(t20_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ C ) =>
% 0.40/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.40/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.62           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.62         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.40/0.62          | (r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.40/0.62          | ~ (v1_relat_1 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['5', '35'])).
% 0.40/0.62  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('38', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.62  thf(t23_funct_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.62       ( ![C:$i]:
% 0.40/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.62             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.40/0.62               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.40/0.62  thf('39', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X18)
% 0.40/0.62          | ~ (v1_funct_1 @ X18)
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 0.40/0.62              = (k1_funct_1 @ X18 @ (k1_funct_1 @ X19 @ X20)))
% 0.40/0.62          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.40/0.62          | ~ (v1_funct_1 @ X19)
% 0.40/0.62          | ~ (v1_relat_1 @ X19))),
% 0.40/0.62      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B)) @ 
% 0.40/0.62        (k4_relat_1 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.40/0.62          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.40/0.62          | ~ (v1_funct_1 @ X22)
% 0.40/0.62          | ~ (v1_relat_1 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.62  thf('45', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62        | ((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | ((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.40/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['42', '45'])).
% 0.40/0.62  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      ((((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.40/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.40/0.62        | ((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['41', '48'])).
% 0.40/0.62  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('52', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.40/0.62  thf('54', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62              = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['40', '53'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ sk_B)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62              = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '54'])).
% 0.40/0.62  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('57', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62              = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ sk_B)
% 0.40/0.62          | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62          | ~ (v2_funct_1 @ sk_B)
% 0.40/0.62          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62              = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '57'])).
% 0.40/0.62  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.40/0.62            = (k1_funct_1 @ X0 @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.40/0.62  thf('63', plain,
% 0.40/0.62      (![X16 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X16)
% 0.40/0.62          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.40/0.62          | ~ (v1_funct_1 @ X16)
% 0.40/0.62          | ~ (v1_relat_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.40/0.62  thf('64', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.40/0.62        | ((sk_A)
% 0.40/0.62            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('65', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.40/0.62                   sk_A))))),
% 0.40/0.62      inference('split', [status(esa)], ['64'])).
% 0.40/0.62  thf('66', plain,
% 0.40/0.62      (((((sk_A)
% 0.40/0.62           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.40/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.40/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62         | ~ (v2_funct_1 @ sk_B)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.40/0.62                   sk_A))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['63', '65'])).
% 0.40/0.62  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('70', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.40/0.62                   sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.40/0.62  thf('71', plain,
% 0.40/0.62      (((sk_D_2 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.40/0.62  thf('72', plain,
% 0.40/0.62      (![X16 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X16)
% 0.40/0.62          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.40/0.62          | ~ (v1_funct_1 @ X16)
% 0.40/0.62          | ~ (v1_relat_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.40/0.62  thf('73', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ sk_B @ 
% 0.40/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.40/0.62      inference('split', [status(esa)], ['64'])).
% 0.40/0.62  thf('74', plain,
% 0.40/0.62      (((((sk_A)
% 0.40/0.62           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.40/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.40/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.40/0.62         | ~ (v2_funct_1 @ sk_B)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ sk_B @ 
% 0.40/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.40/0.62  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('77', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('78', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ sk_B @ 
% 0.40/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.40/0.62  thf('79', plain,
% 0.40/0.62      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B))))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ sk_B @ 
% 0.40/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['71', '78'])).
% 0.40/0.62  thf('80', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.40/0.62  thf('81', plain,
% 0.40/0.62      ((((sk_A) != (sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((sk_A)
% 0.40/0.62                = (k1_funct_1 @ sk_B @ 
% 0.40/0.62                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.40/0.62  thf('82', plain,
% 0.40/0.62      ((((sk_A)
% 0.40/0.62          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['81'])).
% 0.40/0.62  thf('83', plain,
% 0.40/0.62      (~
% 0.40/0.62       (((sk_A)
% 0.40/0.62          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.40/0.62       ~
% 0.40/0.62       (((sk_A)
% 0.40/0.62          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.40/0.62      inference('split', [status(esa)], ['64'])).
% 0.40/0.62  thf('84', plain,
% 0.40/0.62      (~
% 0.40/0.62       (((sk_A)
% 0.40/0.62          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.40/0.62  thf('85', plain,
% 0.40/0.62      (((sk_A)
% 0.40/0.62         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['70', '84'])).
% 0.40/0.62  thf('86', plain,
% 0.40/0.62      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['62', '85'])).
% 0.40/0.62  thf('87', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_2 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.40/0.62  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('89', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('90', plain, (((sk_A) != (sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.40/0.62  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
