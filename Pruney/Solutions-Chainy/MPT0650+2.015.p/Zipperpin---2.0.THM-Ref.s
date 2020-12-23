%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cSpptKK9zY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:20 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 364 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :   26
%              Number of atoms          : 1254 (4975 expanded)
%              Number of equality atoms :   62 ( 305 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('7',plain,(
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

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ X32 )
      | ( X33
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('39',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('40',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t40_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X29 @ X28 ) @ X30 )
      | ( r2_hidden @ X28 @ ( k1_relat_1 @ ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['6','56'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
       != ( k6_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('59',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
        = X25 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','62','63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ sk_A @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) @ X24 )
        = ( k1_funct_1 @ X23 @ ( k1_funct_1 @ X22 @ X24 ) ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ X32 )
      | ( X33
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('82',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74','82'])).

thf('84',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('85',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('93',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('94',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['85'])).

thf('95',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['85'])).

thf('103',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['91','103'])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','104'])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['109','110','111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cSpptKK9zY
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 443 iterations in 0.586s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.84/1.04  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.84/1.04  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.84/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.04  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.84/1.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.84/1.04  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.84/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.04  thf(d9_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.84/1.04  thf('0', plain,
% 0.84/1.04      (![X18 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X18)
% 0.84/1.04          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 0.84/1.04          | ~ (v1_funct_1 @ X18)
% 0.84/1.04          | ~ (v1_relat_1 @ X18))),
% 0.84/1.04      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.84/1.04  thf(dt_k2_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.04       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.84/1.04         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.84/1.04  thf('1', plain,
% 0.84/1.04      (![X19 : $i]:
% 0.84/1.04         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 0.84/1.04          | ~ (v1_funct_1 @ X19)
% 0.84/1.04          | ~ (v1_relat_1 @ X19))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0))),
% 0.84/1.04      inference('sup+', [status(thm)], ['0', '1'])).
% 0.84/1.04  thf('3', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.04  thf(dt_k4_relat_1, axiom,
% 0.84/1.04    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.84/1.04  thf('4', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf('5', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf(t182_relat_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ A ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( v1_relat_1 @ B ) =>
% 0.84/1.04           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.84/1.04             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.84/1.04  thf('6', plain,
% 0.84/1.04      (![X13 : $i, X14 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X13)
% 0.84/1.04          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.84/1.04              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.84/1.04          | ~ (v1_relat_1 @ X14))),
% 0.84/1.04      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.04  thf(t57_funct_1, conjecture,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.84/1.04         ( ( ( A ) =
% 0.84/1.04             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.84/1.04           ( ( A ) =
% 0.84/1.04             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i,B:$i]:
% 0.84/1.04        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.84/1.04            ( ( ( A ) =
% 0.84/1.04                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.84/1.04              ( ( A ) =
% 0.84/1.04                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.84/1.04  thf('7', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(d5_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.84/1.04       ( ![C:$i]:
% 0.84/1.04         ( ( r2_hidden @ C @ B ) <=>
% 0.84/1.04           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.84/1.04  thf('8', plain,
% 0.84/1.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.04         (~ (r2_hidden @ X4 @ X3)
% 0.84/1.04          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.84/1.04          | ((X3) != (k2_relat_1 @ X2)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.84/1.04  thf('9', plain,
% 0.84/1.04      (![X2 : $i, X4 : $i]:
% 0.84/1.04         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.84/1.04          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['8'])).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.84/1.04      inference('sup-', [status(thm)], ['7', '9'])).
% 0.84/1.04  thf(t20_relat_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ C ) =>
% 0.84/1.04       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.84/1.04         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.84/1.04           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.84/1.04  thf('11', plain,
% 0.84/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.84/1.04          | (r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 0.84/1.04          | ~ (v1_relat_1 @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.84/1.04  thf('12', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.04  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('14', plain,
% 0.84/1.04      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['12', '13'])).
% 0.84/1.04  thf('15', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.04  thf('16', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf('17', plain,
% 0.84/1.04      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.84/1.04      inference('sup-', [status(thm)], ['7', '9'])).
% 0.84/1.04  thf('18', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf(d7_relat_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( v1_relat_1 @ A ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( v1_relat_1 @ B ) =>
% 0.84/1.04           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.84/1.04             ( ![C:$i,D:$i]:
% 0.84/1.04               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.84/1.04                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.84/1.04  thf('19', plain,
% 0.84/1.04      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X7)
% 0.84/1.04          | ((X7) != (k4_relat_1 @ X8))
% 0.84/1.04          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 0.84/1.04          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X8)
% 0.84/1.04          | ~ (v1_relat_1 @ X8))),
% 0.84/1.04      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.84/1.04  thf('20', plain,
% 0.84/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X8)
% 0.84/1.04          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X8)
% 0.84/1.04          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ (k4_relat_1 @ X8))
% 0.84/1.04          | ~ (v1_relat_1 @ (k4_relat_1 @ X8)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['19'])).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X0)
% 0.84/1.04          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.84/1.04          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['18', '20'])).
% 0.84/1.04  thf('22', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.84/1.04          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.84/1.04          | ~ (v1_relat_1 @ X0))),
% 0.84/1.04      inference('simplify', [status(thm)], ['21'])).
% 0.84/1.04  thf('23', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.84/1.04           (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['17', '22'])).
% 0.84/1.04  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('25', plain,
% 0.84/1.04      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.84/1.04        (k4_relat_1 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['23', '24'])).
% 0.84/1.04  thf(t8_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.84/1.04         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.84/1.04           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.84/1.04  thf('26', plain,
% 0.84/1.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ X32)
% 0.84/1.04          | ((X33) = (k1_funct_1 @ X32 @ X31))
% 0.84/1.04          | ~ (v1_funct_1 @ X32)
% 0.84/1.04          | ~ (v1_relat_1 @ X32))),
% 0.84/1.04      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.84/1.04  thf('27', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['25', '26'])).
% 0.84/1.04  thf('28', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['16', '27'])).
% 0.84/1.04  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['28', '29'])).
% 0.84/1.04  thf('31', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04        | ~ (v2_funct_1 @ sk_B)
% 0.84/1.04        | ((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['15', '30'])).
% 0.84/1.04  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('34', plain, ((v2_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('35', plain,
% 0.84/1.04      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.84/1.04      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      ((r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.84/1.04        (k1_relat_1 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['14', '35'])).
% 0.84/1.04  thf('37', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.04  thf('38', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf('39', plain,
% 0.84/1.04      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.84/1.04  thf('40', plain,
% 0.84/1.04      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.84/1.04        (k4_relat_1 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['23', '24'])).
% 0.84/1.04  thf('41', plain,
% 0.84/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.84/1.04          | (r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 0.84/1.04          | ~ (v1_relat_1 @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.84/1.04  thf('42', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.04  thf('43', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['39', '42'])).
% 0.84/1.04  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('45', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['43', '44'])).
% 0.84/1.04  thf(t40_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04       ( ( r2_hidden @
% 0.84/1.04           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.84/1.04         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.84/1.04           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.84/1.04  thf('46', plain,
% 0.84/1.04      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.84/1.04         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.84/1.04          | ~ (r2_hidden @ (k1_funct_1 @ X29 @ X28) @ X30)
% 0.84/1.04          | (r2_hidden @ X28 @ 
% 0.84/1.04             (k1_relat_1 @ (k5_relat_1 @ X29 @ (k6_relat_1 @ X30))))
% 0.84/1.04          | ~ (v1_funct_1 @ X29)
% 0.84/1.04          | ~ (v1_relat_1 @ X29))),
% 0.84/1.04      inference('cnf', [status(esa)], [t40_funct_1])).
% 0.84/1.04  thf('47', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04          | (r2_hidden @ sk_A @ 
% 0.84/1.04             (k1_relat_1 @ 
% 0.84/1.04              (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0))))
% 0.84/1.04          | ~ (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['45', '46'])).
% 0.84/1.04  thf('48', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ sk_B)
% 0.84/1.04          | ~ (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.84/1.04          | (r2_hidden @ sk_A @ 
% 0.84/1.04             (k1_relat_1 @ 
% 0.84/1.04              (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0))))
% 0.84/1.04          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['38', '47'])).
% 0.84/1.04  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('50', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.84/1.04          | (r2_hidden @ sk_A @ 
% 0.84/1.04             (k1_relat_1 @ 
% 0.84/1.04              (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0))))
% 0.84/1.04          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['48', '49'])).
% 0.84/1.04  thf('51', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ sk_B)
% 0.84/1.04          | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04          | ~ (v2_funct_1 @ sk_B)
% 0.84/1.04          | (r2_hidden @ sk_A @ 
% 0.84/1.04             (k1_relat_1 @ 
% 0.84/1.04              (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0))))
% 0.84/1.04          | ~ (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['37', '50'])).
% 0.84/1.04  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('54', plain, ((v2_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('55', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((r2_hidden @ sk_A @ 
% 0.84/1.04           (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0))))
% 0.84/1.04          | ~ (r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ X0))),
% 0.84/1.04      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.84/1.04  thf('56', plain,
% 0.84/1.04      ((r2_hidden @ sk_A @ 
% 0.84/1.04        (k1_relat_1 @ 
% 0.84/1.04         (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['36', '55'])).
% 0.84/1.04  thf('57', plain,
% 0.84/1.04      (((r2_hidden @ sk_A @ 
% 0.84/1.04         (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 0.84/1.04          (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))))
% 0.84/1.04        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.84/1.04      inference('sup+', [status(thm)], ['6', '56'])).
% 0.84/1.04  thf(t34_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.84/1.04         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.84/1.04           ( ![C:$i]:
% 0.84/1.04             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.84/1.04  thf('58', plain,
% 0.84/1.04      (![X25 : $i, X26 : $i]:
% 0.84/1.04         (((X26) != (k6_relat_1 @ X25))
% 0.84/1.04          | ((k1_relat_1 @ X26) = (X25))
% 0.84/1.04          | ~ (v1_funct_1 @ X26)
% 0.84/1.04          | ~ (v1_relat_1 @ X26))),
% 0.84/1.04      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.84/1.04  thf('59', plain,
% 0.84/1.04      (![X25 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ (k6_relat_1 @ X25))
% 0.84/1.04          | ~ (v1_funct_1 @ (k6_relat_1 @ X25))
% 0.84/1.04          | ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['58'])).
% 0.84/1.04  thf(fc3_funct_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.84/1.04       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.84/1.04  thf('60', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.84/1.04  thf('61', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.84/1.04  thf('62', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.84/1.04      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.84/1.04  thf('63', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.84/1.04  thf('64', plain,
% 0.84/1.04      (((r2_hidden @ sk_A @ 
% 0.84/1.04         (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))
% 0.84/1.04        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['57', '62', '63'])).
% 0.84/1.04  thf('65', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | (r2_hidden @ sk_A @ 
% 0.84/1.04           (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['5', '64'])).
% 0.84/1.04  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('67', plain,
% 0.84/1.04      ((r2_hidden @ sk_A @ 
% 0.84/1.04        (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['65', '66'])).
% 0.84/1.04  thf('68', plain,
% 0.84/1.04      (![X13 : $i, X14 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X13)
% 0.84/1.04          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.84/1.04              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.84/1.04          | ~ (v1_relat_1 @ X14))),
% 0.84/1.04      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.04  thf(t22_funct_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.04       ( ![C:$i]:
% 0.84/1.04         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.84/1.04           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.84/1.04             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.84/1.04               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.84/1.04  thf('69', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.04         (~ (v1_relat_1 @ X22)
% 0.84/1.04          | ~ (v1_funct_1 @ X22)
% 0.84/1.04          | ((k1_funct_1 @ (k5_relat_1 @ X22 @ X23) @ X24)
% 0.84/1.04              = (k1_funct_1 @ X23 @ (k1_funct_1 @ X22 @ X24)))
% 0.84/1.04          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ (k5_relat_1 @ X22 @ X23)))
% 0.84/1.04          | ~ (v1_funct_1 @ X23)
% 0.84/1.04          | ~ (v1_relat_1 @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.84/1.04  thf('70', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.84/1.04              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.84/1.04          | ~ (v1_funct_1 @ X1)
% 0.84/1.04          | ~ (v1_relat_1 @ X1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['68', '69'])).
% 0.84/1.04  thf('71', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (v1_funct_1 @ X1)
% 0.84/1.04          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.84/1.04              = (k1_funct_1 @ X0 @ (k1_funct_1 @ X1 @ X2)))
% 0.84/1.04          | ~ (v1_funct_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X0)
% 0.84/1.04          | ~ (v1_relat_1 @ X1)
% 0.84/1.04          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.84/1.04      inference('simplify', [status(thm)], ['70'])).
% 0.84/1.04  thf('72', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.84/1.04            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['67', '71'])).
% 0.84/1.04  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('75', plain,
% 0.84/1.04      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.84/1.04      inference('sup-', [status(thm)], ['7', '9'])).
% 0.84/1.04  thf('76', plain,
% 0.84/1.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.84/1.04         (~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ X32)
% 0.84/1.04          | ((X33) = (k1_funct_1 @ X32 @ X31))
% 0.84/1.04          | ~ (v1_funct_1 @ X32)
% 0.84/1.04          | ~ (v1_relat_1 @ X32))),
% 0.84/1.04      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.84/1.04  thf('77', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B)
% 0.84/1.04        | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['75', '76'])).
% 0.84/1.04  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('80', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.84/1.04  thf('81', plain,
% 0.84/1.04      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.84/1.04      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.84/1.04  thf('82', plain,
% 0.84/1.04      (((sk_A)
% 0.84/1.04         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['80', '81'])).
% 0.84/1.04  thf('83', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.84/1.04            = (sk_A))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['72', '73', '74', '82'])).
% 0.84/1.04  thf('84', plain,
% 0.84/1.04      (![X18 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X18)
% 0.84/1.04          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 0.84/1.04          | ~ (v1_funct_1 @ X18)
% 0.84/1.04          | ~ (v1_relat_1 @ X18))),
% 0.84/1.04      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.84/1.04  thf('85', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.84/1.04        | ((sk_A)
% 0.84/1.04            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('86', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.84/1.04                   sk_A))))),
% 0.84/1.04      inference('split', [status(esa)], ['85'])).
% 0.84/1.04  thf('87', plain,
% 0.84/1.04      (((((sk_A)
% 0.84/1.04           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.84/1.04         | ~ (v1_relat_1 @ sk_B)
% 0.84/1.04         | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04         | ~ (v2_funct_1 @ sk_B)))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.84/1.04                   sk_A))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['84', '86'])).
% 0.84/1.04  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('89', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('90', plain, ((v2_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('91', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.84/1.04                   sk_A))))),
% 0.84/1.04      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.84/1.04  thf('92', plain,
% 0.84/1.04      (((sk_A)
% 0.84/1.04         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['80', '81'])).
% 0.84/1.04  thf('93', plain,
% 0.84/1.04      (![X18 : $i]:
% 0.84/1.04         (~ (v2_funct_1 @ X18)
% 0.84/1.04          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 0.84/1.04          | ~ (v1_funct_1 @ X18)
% 0.84/1.04          | ~ (v1_relat_1 @ X18))),
% 0.84/1.04      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.84/1.04  thf('94', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ sk_B @ 
% 0.84/1.04                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.84/1.04      inference('split', [status(esa)], ['85'])).
% 0.84/1.04  thf('95', plain,
% 0.84/1.04      (((((sk_A)
% 0.84/1.04           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.84/1.04         | ~ (v1_relat_1 @ sk_B)
% 0.84/1.04         | ~ (v1_funct_1 @ sk_B)
% 0.84/1.04         | ~ (v2_funct_1 @ sk_B)))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ sk_B @ 
% 0.84/1.04                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['93', '94'])).
% 0.84/1.04  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('98', plain, ((v2_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('99', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ sk_B @ 
% 0.84/1.04                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.84/1.04      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.84/1.04  thf('100', plain,
% 0.84/1.04      ((((sk_A) != (sk_A)))
% 0.84/1.04         <= (~
% 0.84/1.04             (((sk_A)
% 0.84/1.04                = (k1_funct_1 @ sk_B @ 
% 0.84/1.04                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['92', '99'])).
% 0.84/1.04  thf('101', plain,
% 0.84/1.04      ((((sk_A)
% 0.84/1.04          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.84/1.04      inference('simplify', [status(thm)], ['100'])).
% 0.84/1.04  thf('102', plain,
% 0.84/1.04      (~
% 0.84/1.04       (((sk_A)
% 0.84/1.04          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.84/1.04       ~
% 0.84/1.04       (((sk_A)
% 0.84/1.04          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.84/1.04      inference('split', [status(esa)], ['85'])).
% 0.84/1.04  thf('103', plain,
% 0.84/1.04      (~
% 0.84/1.04       (((sk_A)
% 0.84/1.04          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.84/1.04      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 0.84/1.04  thf('104', plain,
% 0.84/1.04      (((sk_A)
% 0.84/1.04         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.84/1.04      inference('simpl_trail', [status(thm)], ['91', '103'])).
% 0.84/1.04  thf('105', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.84/1.04        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('simplify_reflect-', [status(thm)], ['83', '104'])).
% 0.84/1.04  thf('106', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['4', '105'])).
% 0.84/1.04  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('108', plain, (~ (v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['106', '107'])).
% 0.84/1.04  thf('109', plain,
% 0.84/1.04      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['3', '108'])).
% 0.84/1.04  thf('110', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('111', plain, ((v1_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('112', plain, ((v2_funct_1 @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('113', plain, ($false),
% 0.84/1.04      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.84/1.04  
% 0.84/1.04  % SZS output end Refutation
% 0.84/1.04  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
