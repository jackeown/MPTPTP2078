%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lZN3FETs4Z

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:33 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 333 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  798 (7252 expanded)
%              Number of equality atoms :   68 ( 808 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t60_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k1_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i,D: $i] :
                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                      & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                   => ( ( ( k1_funct_1 @ A @ C )
                        = D )
                    <=> ( ( k1_funct_1 @ B @ D )
                        = C ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_1])).

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_funct_1,axiom,(
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

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('20',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ( X15
        = ( k1_funct_1 @ ( k2_funct_1 @ X14 ) @ ( k1_funct_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_A @ X18 )
        = X19 )
      | ( ( k1_funct_1 @ sk_B @ X19 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X19 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X19 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('56',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X19 ) )
        = X19 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    = ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C @ X16 @ X17 ) ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('65',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('66',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66'])).

thf('68',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lZN3FETs4Z
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.35/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.53  % Solved by: fo/fo7.sh
% 1.35/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.53  % done 1320 iterations in 1.094s
% 1.35/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.53  % SZS output start Refutation
% 1.35/1.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.35/1.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.35/1.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.35/1.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.35/1.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.35/1.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.53  thf(t60_funct_1, conjecture,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.53       ( ![B:$i]:
% 1.35/1.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.53           ( ( ( v2_funct_1 @ A ) & 
% 1.35/1.53               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 1.35/1.53               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.35/1.53               ( ![C:$i,D:$i]:
% 1.35/1.53                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.35/1.53                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 1.35/1.53                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 1.35/1.53                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 1.35/1.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.35/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.53    (~( ![A:$i]:
% 1.35/1.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.53          ( ![B:$i]:
% 1.35/1.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.53              ( ( ( v2_funct_1 @ A ) & 
% 1.35/1.53                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 1.35/1.53                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.35/1.53                  ( ![C:$i,D:$i]:
% 1.35/1.53                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.35/1.53                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 1.35/1.53                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 1.35/1.53                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 1.35/1.53                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 1.35/1.53    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 1.35/1.53  thf('0', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(d9_funct_1, axiom,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.35/1.53  thf('1', plain,
% 1.35/1.53      (![X8 : $i]:
% 1.35/1.53         (~ (v2_funct_1 @ X8)
% 1.35/1.53          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.35/1.53          | ~ (v1_funct_1 @ X8)
% 1.35/1.53          | ~ (v1_relat_1 @ X8))),
% 1.35/1.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.35/1.53  thf('2', plain,
% 1.35/1.53      ((~ (v1_funct_1 @ sk_A)
% 1.35/1.53        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 1.35/1.53        | ~ (v2_funct_1 @ sk_A))),
% 1.35/1.53      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.53  thf('3', plain, ((v1_funct_1 @ sk_A)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('4', plain, ((v2_funct_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('5', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.35/1.54  thf(t37_relat_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( v1_relat_1 @ A ) =>
% 1.35/1.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.35/1.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.35/1.54  thf('6', plain,
% 1.35/1.54      (![X2 : $i]:
% 1.35/1.54         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 1.35/1.54          | ~ (v1_relat_1 @ X2))),
% 1.35/1.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.35/1.54  thf('7', plain,
% 1.35/1.54      ((((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.35/1.54        | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['5', '6'])).
% 1.35/1.54  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('9', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)], ['7', '8'])).
% 1.35/1.54  thf('10', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t9_funct_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.54       ( ![B:$i]:
% 1.35/1.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.54           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.35/1.54               ( ![C:$i]:
% 1.35/1.54                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.35/1.54                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.35/1.54             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.35/1.54  thf('11', plain,
% 1.35/1.54      (![X16 : $i, X17 : $i]:
% 1.35/1.54         (~ (v1_relat_1 @ X16)
% 1.35/1.54          | ~ (v1_funct_1 @ X16)
% 1.35/1.54          | ((X17) = (X16))
% 1.35/1.54          | (r2_hidden @ (sk_C @ X16 @ X17) @ (k1_relat_1 @ X17))
% 1.35/1.54          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 1.35/1.54          | ~ (v1_funct_1 @ X17)
% 1.35/1.54          | ~ (v1_relat_1 @ X17))),
% 1.35/1.54      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.35/1.54  thf('12', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (((k2_relat_1 @ sk_A) != (k1_relat_1 @ X0))
% 1.35/1.54          | ~ (v1_relat_1 @ sk_B)
% 1.35/1.54          | ~ (v1_funct_1 @ sk_B)
% 1.35/1.54          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.35/1.54          | ((sk_B) = (X0))
% 1.35/1.54          | ~ (v1_funct_1 @ X0)
% 1.35/1.54          | ~ (v1_relat_1 @ X0))),
% 1.35/1.54      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.54  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('15', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('16', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (((k2_relat_1 @ sk_A) != (k1_relat_1 @ X0))
% 1.35/1.54          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | ((sk_B) = (X0))
% 1.35/1.54          | ~ (v1_funct_1 @ X0)
% 1.35/1.54          | ~ (v1_relat_1 @ X0))),
% 1.35/1.54      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.35/1.54  thf('17', plain,
% 1.35/1.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 1.35/1.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 1.35/1.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.35/1.54        | ((sk_B) = (k2_funct_1 @ sk_A))
% 1.35/1.54        | (r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 1.35/1.54           (k2_relat_1 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['9', '16'])).
% 1.35/1.54  thf('18', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.35/1.54  thf(dt_k4_relat_1, axiom,
% 1.35/1.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.35/1.54  thf('19', plain,
% 1.35/1.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.35/1.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.35/1.54  thf('20', plain,
% 1.35/1.54      (((v1_relat_1 @ (k2_funct_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['18', '19'])).
% 1.35/1.54  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('22', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['20', '21'])).
% 1.35/1.54  thf('23', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.35/1.54  thf(fc5_funct_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.35/1.54       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 1.35/1.54         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 1.35/1.54  thf('24', plain,
% 1.35/1.54      (![X11 : $i]:
% 1.35/1.54         ((v1_funct_1 @ (k4_relat_1 @ X11))
% 1.35/1.54          | ~ (v2_funct_1 @ X11)
% 1.35/1.54          | ~ (v1_funct_1 @ X11)
% 1.35/1.54          | ~ (v1_relat_1 @ X11))),
% 1.35/1.54      inference('cnf', [status(esa)], [fc5_funct_1])).
% 1.35/1.54  thf('25', plain,
% 1.35/1.54      (((v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.35/1.54        | ~ (v1_relat_1 @ sk_A)
% 1.35/1.54        | ~ (v1_funct_1 @ sk_A)
% 1.35/1.54        | ~ (v2_funct_1 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['23', '24'])).
% 1.35/1.54  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('28', plain, ((v2_funct_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.35/1.54  thf('30', plain,
% 1.35/1.54      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 1.35/1.54        | ((sk_B) = (k2_funct_1 @ sk_A))
% 1.35/1.54        | (r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 1.35/1.54           (k2_relat_1 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)], ['17', '22', '29'])).
% 1.35/1.54  thf('31', plain,
% 1.35/1.54      (((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))
% 1.35/1.54        | ((sk_B) = (k2_funct_1 @ sk_A)))),
% 1.35/1.54      inference('simplify', [status(thm)], ['30'])).
% 1.35/1.54  thf('32', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('33', plain,
% 1.35/1.54      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 1.35/1.54      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.35/1.54  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t12_funct_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.35/1.54         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 1.35/1.54  thf('35', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 1.35/1.54          | (r2_hidden @ (k1_funct_1 @ X13 @ X12) @ (k2_relat_1 @ X13))
% 1.35/1.54          | ~ (v1_funct_1 @ X13)
% 1.35/1.54          | ~ (v1_relat_1 @ X13))),
% 1.35/1.54      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.35/1.54  thf('36', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | ~ (v1_relat_1 @ sk_B)
% 1.35/1.54          | ~ (v1_funct_1 @ sk_B)
% 1.35/1.54          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['34', '35'])).
% 1.35/1.54  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('39', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.35/1.54  thf('40', plain,
% 1.35/1.54      ((r2_hidden @ 
% 1.35/1.54        (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 1.35/1.54        (k2_relat_1 @ sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['33', '39'])).
% 1.35/1.54  thf('41', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(t56_funct_1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.54       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 1.35/1.54         ( ( ( A ) =
% 1.35/1.54             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 1.35/1.54           ( ( A ) =
% 1.35/1.54             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 1.35/1.54  thf('42', plain,
% 1.35/1.54      (![X14 : $i, X15 : $i]:
% 1.35/1.54         (~ (v2_funct_1 @ X14)
% 1.35/1.54          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 1.35/1.54          | ((X15)
% 1.35/1.54              = (k1_funct_1 @ (k2_funct_1 @ X14) @ (k1_funct_1 @ X14 @ X15)))
% 1.35/1.54          | ~ (v1_funct_1 @ X14)
% 1.35/1.54          | ~ (v1_relat_1 @ X14))),
% 1.35/1.54      inference('cnf', [status(esa)], [t56_funct_1])).
% 1.35/1.54  thf('43', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 1.35/1.54          | ~ (v1_relat_1 @ sk_A)
% 1.35/1.54          | ~ (v1_funct_1 @ sk_A)
% 1.35/1.54          | ((X0)
% 1.35/1.54              = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0)))
% 1.35/1.54          | ~ (v2_funct_1 @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['41', '42'])).
% 1.35/1.54  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('47', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 1.35/1.54          | ((X0)
% 1.35/1.54              = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0))))),
% 1.35/1.54      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 1.35/1.54  thf('48', plain,
% 1.35/1.54      (((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 1.35/1.54         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.35/1.54            (k1_funct_1 @ sk_A @ 
% 1.35/1.54             (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['40', '47'])).
% 1.35/1.54  thf('49', plain,
% 1.35/1.54      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 1.35/1.54      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.35/1.54  thf('50', plain,
% 1.35/1.54      (![X18 : $i, X19 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X18 @ (k1_relat_1 @ sk_A))
% 1.35/1.54          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ sk_B))
% 1.35/1.54          | ((k1_funct_1 @ sk_A @ X18) = (X19))
% 1.35/1.54          | ((k1_funct_1 @ sk_B @ X19) != (X18)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('51', plain,
% 1.35/1.54      (![X19 : $i]:
% 1.35/1.54         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X19)) = (X19))
% 1.35/1.54          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ sk_B))
% 1.35/1.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X19) @ (k1_relat_1 @ sk_A)))),
% 1.35/1.54      inference('simplify', [status(thm)], ['50'])).
% 1.35/1.54  thf('52', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('53', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('54', plain,
% 1.35/1.54      (![X19 : $i]:
% 1.35/1.54         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X19)) = (X19))
% 1.35/1.54          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X19) @ (k2_relat_1 @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.35/1.54  thf('55', plain,
% 1.35/1.54      (![X0 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.35/1.54  thf('56', plain,
% 1.35/1.54      (![X19 : $i]:
% 1.35/1.54         (~ (r2_hidden @ X19 @ (k2_relat_1 @ sk_A))
% 1.35/1.54          | ((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X19)) = (X19)))),
% 1.35/1.54      inference('clc', [status(thm)], ['54', '55'])).
% 1.35/1.54  thf('57', plain,
% 1.35/1.54      (((k1_funct_1 @ sk_A @ 
% 1.35/1.54         (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 1.35/1.54         = (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['49', '56'])).
% 1.35/1.54  thf('58', plain,
% 1.35/1.54      (((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 1.35/1.54         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 1.35/1.54            (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))),
% 1.35/1.54      inference('demod', [status(thm)], ['48', '57'])).
% 1.35/1.54  thf('59', plain,
% 1.35/1.54      (![X16 : $i, X17 : $i]:
% 1.35/1.54         (~ (v1_relat_1 @ X16)
% 1.35/1.54          | ~ (v1_funct_1 @ X16)
% 1.35/1.54          | ((X17) = (X16))
% 1.35/1.54          | ((k1_funct_1 @ X17 @ (sk_C @ X16 @ X17))
% 1.35/1.54              != (k1_funct_1 @ X16 @ (sk_C @ X16 @ X17)))
% 1.35/1.54          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 1.35/1.54          | ~ (v1_funct_1 @ X17)
% 1.35/1.54          | ~ (v1_relat_1 @ X17))),
% 1.35/1.54      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.35/1.54  thf('60', plain,
% 1.35/1.54      ((((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 1.35/1.54          != (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 1.35/1.54        | ~ (v1_relat_1 @ sk_B)
% 1.35/1.54        | ~ (v1_funct_1 @ sk_B)
% 1.35/1.54        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 1.35/1.54        | ((sk_B) = (k2_funct_1 @ sk_A))
% 1.35/1.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 1.35/1.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['58', '59'])).
% 1.35/1.54  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('63', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('64', plain,
% 1.35/1.54      (((k2_relat_1 @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)], ['7', '8'])).
% 1.35/1.54  thf('65', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.35/1.54  thf('66', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['20', '21'])).
% 1.35/1.54  thf('67', plain,
% 1.35/1.54      ((((k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B))
% 1.35/1.54          != (k1_funct_1 @ sk_B @ (sk_C @ (k2_funct_1 @ sk_A) @ sk_B)))
% 1.35/1.54        | ((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 1.35/1.54        | ((sk_B) = (k2_funct_1 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)],
% 1.35/1.54                ['60', '61', '62', '63', '64', '65', '66'])).
% 1.35/1.54  thf('68', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('simplify', [status(thm)], ['67'])).
% 1.35/1.54  thf('69', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('70', plain, ($false),
% 1.35/1.54      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 1.35/1.54  
% 1.35/1.54  % SZS output end Refutation
% 1.35/1.54  
% 1.35/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
