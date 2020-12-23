%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NWuq9svJ0w

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 249 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  898 (3479 expanded)
%              Number of equality atoms :   54 ( 228 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k1_funct_1 @ X18 @ ( k1_funct_1 @ X19 @ X20 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('34',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('62',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('63',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('71',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['40','71'])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NWuq9svJ0w
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 177 iterations in 0.090s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.57  thf(d9_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X16 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X16)
% 0.21/0.57          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.21/0.57          | ~ (v1_funct_1 @ X16)
% 0.21/0.57          | ~ (v1_relat_1 @ X16))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf(dt_k2_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 0.21/0.57          | ~ (v1_funct_1 @ X17)
% 0.21/0.57          | ~ (v1_relat_1 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v2_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.57  thf(dt_k4_relat_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf(t57_funct_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.57         ( ( ( A ) =
% 0.21/0.57             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.57           ( ( A ) =
% 0.21/0.57             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.57            ( ( ( A ) =
% 0.21/0.57                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.57              ( ( A ) =
% 0.21/0.57                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.21/0.57  thf('6', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d5_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.57          | ((X3) != (k2_relat_1 @ X2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X2 : $i, X4 : $i]:
% 0.21/0.57         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.57          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf(d7_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( v1_relat_1 @ B ) =>
% 0.21/0.57           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.21/0.57             ( ![C:$i,D:$i]:
% 0.21/0.57               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.57                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X7)
% 0.21/0.57          | ((X7) != (k4_relat_1 @ X8))
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 0.21/0.57          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X8)
% 0.21/0.57          | ~ (v1_relat_1 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X8)
% 0.21/0.57          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X8)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ (k4_relat_1 @ X8))
% 0.21/0.57          | ~ (v1_relat_1 @ (k4_relat_1 @ X8)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.21/0.57           (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.57  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.21/0.57        (k4_relat_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf(t20_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ C ) =>
% 0.21/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.57           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.21/0.57          | (r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 0.21/0.57          | ~ (v1_relat_1 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.21/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '19'])).
% 0.21/0.57  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf(t23_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.57             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.57               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X18)
% 0.21/0.57          | ~ (v1_funct_1 @ X18)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 0.21/0.57              = (k1_funct_1 @ X18 @ (k1_funct_1 @ X19 @ X20)))
% 0.21/0.57          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.21/0.57          | ~ (v1_funct_1 @ X19)
% 0.21/0.57          | ~ (v1_relat_1 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.21/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ sk_B)
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '24'])).
% 0.21/0.57  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57          | ~ (v2_funct_1 @ sk_B)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '27'])).
% 0.21/0.57  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.21/0.57            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X16 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X16)
% 0.21/0.57          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.21/0.57          | ~ (v1_funct_1 @ X16)
% 0.21/0.57          | ~ (v1_relat_1 @ X16))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.57        | ((sk_A)
% 0.21/0.57            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.57                   sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (((((sk_A)
% 0.21/0.57           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.57                   sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '35'])).
% 0.21/0.57  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('39', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.57                   sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.57  thf(t8_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.21/0.57          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.21/0.57          | ~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v1_relat_1 @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.21/0.57        (k4_relat_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.21/0.57          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 0.21/0.57          | ~ (v1_funct_1 @ X22)
% 0.21/0.57          | ~ (v1_relat_1 @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.21/0.57        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.21/0.57        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.57  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.21/0.57        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.57        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '54'])).
% 0.21/0.57  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('58', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (((sk_A)
% 0.21/0.57         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (![X16 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X16)
% 0.21/0.57          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.21/0.57          | ~ (v1_funct_1 @ X16)
% 0.21/0.57          | ~ (v1_relat_1 @ X16))),
% 0.21/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ sk_B @ 
% 0.21/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['34'])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (((((sk_A)
% 0.21/0.57           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ sk_B @ 
% 0.21/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('66', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ sk_B @ 
% 0.21/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      ((((sk_A) != (sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((sk_A)
% 0.21/0.57                = (k1_funct_1 @ sk_B @ 
% 0.21/0.57                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '67'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((sk_A)
% 0.21/0.57          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.21/0.57       ~
% 0.21/0.57       (((sk_A)
% 0.21/0.57          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['34'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((sk_A)
% 0.21/0.57          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (((sk_A)
% 0.21/0.57         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['40', '71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      ((((sk_A)
% 0.21/0.57          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '72'])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (((sk_A)
% 0.21/0.57         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '59'])).
% 0.21/0.57  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('77', plain, (((sk_A) != (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.21/0.57  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
