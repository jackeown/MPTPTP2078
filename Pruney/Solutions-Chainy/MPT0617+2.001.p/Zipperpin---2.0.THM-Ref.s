%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pNhXKkvKh7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 168 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  825 (2533 expanded)
%              Number of equality atoms :   30 ( 186 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t9_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i] :
                    ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                   => ( ( k1_funct_1 @ A @ C )
                      = ( k1_funct_1 @ B @ C ) ) ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_1])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X18 )
        = ( k1_funct_1 @ sk_B @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X18: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X18 )
        = ( k1_funct_1 @ sk_B @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_A ) )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_D @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X3 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X18 )
        = ( k1_funct_1 @ sk_B @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X3 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('68',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['39','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pNhXKkvKh7
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 99 iterations in 0.059s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(d3_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51           ( ![C:$i,D:$i]:
% 0.20/0.51             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.20/0.51               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 0.20/0.51          | (r1_tarski @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.51  thf(t8_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.51          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf(t9_funct_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.51               ( ![C:$i]:
% 0.20/0.51                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.51                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.51             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51              ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.51                  ( ![C:$i]:
% 0.20/0.51                    ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.51                      ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.51                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t9_funct_1])).
% 0.20/0.51  thf('4', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 0.20/0.51          | (r1_tarski @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.51          | (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '8'])).
% 0.20/0.51  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X18 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_A @ X18) = (k1_funct_1 @ sk_B @ X18))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X18 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_A @ X18) = (k1_funct_1 @ sk_B @ X18))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | ((k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_A))
% 0.20/0.51              = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_D @ X0 @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A)))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '16'])).
% 0.20/0.51  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_D @ X0 @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A)))
% 0.20/0.51          | (r1_tarski @ sk_A @ X0)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | ((sk_D @ X0 @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.51          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X16)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.20/0.51          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.51              (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A))) @ 
% 0.20/0.51             sk_B)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.51  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.51              (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_A))) @ 
% 0.20/0.51             sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ 
% 0.20/0.51           sk_B)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X3)
% 0.20/0.51          | (r1_tarski @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.51        | (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('37', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X18 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_A @ X18) = (k1_funct_1 @ sk_B @ X18))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | ((k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))
% 0.20/0.51              = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ((k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))
% 0.20/0.51              = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 0.20/0.51          | (r1_tarski @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.51  thf(d4_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.20/0.51          | (r2_hidden @ X8 @ X11)
% 0.20/0.51          | ((X11) != (k1_relat_1 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.20/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r1_tarski @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '49'])).
% 0.20/0.51  thf('51', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X16)
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.20/0.51          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.51              (k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))) @ 
% 0.20/0.51             sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.51  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.51              (k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))) @ 
% 0.20/0.51             sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ 
% 0.20/0.51           (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.51            (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['46', '59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.51              (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))) @ 
% 0.20/0.51             sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['40', '61'])).
% 0.20/0.51  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_B @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_D @ X0 @ sk_B)) @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X3)
% 0.20/0.51          | (r1_tarski @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.51  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.51  thf('72', plain, ($false), inference('demod', [status(thm)], ['39', '71'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
