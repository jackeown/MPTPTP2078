%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xyGrrAyuOr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  680 (1408 expanded)
%              Number of equality atoms :   40 (  87 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t53_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ? [B: $i] :
              ( ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
              & ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

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

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k6_relat_1 @ X10 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
        = X12 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('4',plain,(
    ! [X10: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X10 ) @ X12 )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X4: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X10 ) @ X12 )
        = X12 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_C @ X0 ) )
        = ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_A ) )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_A ) )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_A ) )
    = ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

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

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( sk_C @ sk_A )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('31',plain,(
    ! [X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X10 ) @ X12 )
        = X12 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_A ) )
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C @ sk_A )
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('47',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xyGrrAyuOr
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 67 iterations in 0.075s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(t53_funct_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( ?[B:$i]:
% 0.20/0.53           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.53             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.20/0.53         ( v2_funct_1 @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53          ( ( ?[B:$i]:
% 0.20/0.53              ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.53                ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.20/0.53            ( v2_funct_1 @ A ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t53_funct_1])).
% 0.20/0.53  thf('0', plain, (~ (v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d8_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.53         ( ![B:$i,C:$i]:
% 0.20/0.53           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf(t34_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.53         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (((X11) != (k6_relat_1 @ X10))
% 0.20/0.53          | ((k1_funct_1 @ X11 @ X12) = (X12))
% 0.20/0.53          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ~ (v1_funct_1 @ X11)
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ (k6_relat_1 @ X10))
% 0.20/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ X10))
% 0.20/0.53          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ((k1_funct_1 @ (k6_relat_1 @ X10) @ X12) = (X12)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.53  thf(fc3_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.53  thf('5', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.53  thf('6', plain, (![X4 : $i]: (v1_funct_1 @ (k6_relat_1 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ((k1_funct_1 @ (k6_relat_1 @ X10) @ X12) = (X12)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ (sk_C @ X0))
% 0.20/0.53              = (sk_C @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_C @ sk_A))
% 0.20/0.53          = (sk_C @ sk_A))
% 0.20/0.53        | (v2_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['1', '8'])).
% 0.20/0.53  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_C @ sk_A))
% 0.20/0.53          = (sk_C @ sk_A))
% 0.20/0.53        | (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.53  thf('13', plain, (~ (v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_C @ sk_A))
% 0.20/0.53         = (sk_C @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf(t23_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.53             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.53               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.53              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.20/0.53          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.53          | ~ (v1_funct_1 @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 0.20/0.53              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))
% 0.20/0.53              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.53              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.20/0.53          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.53          | ~ (v1_funct_1 @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C @ X0))))
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_C @ X0))))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53            = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['19', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X0 @ (sk_B @ X0)))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53            = (k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_C @ X0))
% 0.20/0.53              = (k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ (sk_B @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((sk_C @ sk_A)
% 0.20/0.53          = (k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_A)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | (v2_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.53          | ((k1_funct_1 @ (k6_relat_1 @ X10) @ X12) = (X12)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ((k1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ (sk_B @ X0))
% 0.20/0.53              = (sk_B @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_A))
% 0.20/0.53          = (sk_B @ sk_A))
% 0.20/0.53        | (v2_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['29', '32'])).
% 0.20/0.53  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_A))
% 0.20/0.53          = (sk_B @ sk_A))
% 0.20/0.53        | (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.53  thf('37', plain, (~ (v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((k1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_A))
% 0.20/0.53         = (sk_B @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain, ((((sk_C @ sk_A) = (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '38', '39', '40', '41', '42'])).
% 0.20/0.53  thf('44', plain, (~ (v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, (((sk_C @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B @ X0) != (sk_C @ X0))
% 0.20/0.53          | (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((((sk_B @ sk_A) != (sk_B @ sk_A))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.53  thf('51', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
