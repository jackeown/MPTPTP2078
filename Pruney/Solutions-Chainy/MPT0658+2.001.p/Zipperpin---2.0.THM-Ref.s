%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MfXXnd73Pg

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 253 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  615 (2203 expanded)
%              Number of equality atoms :   54 ( 185 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t65_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_1])).

thf('2',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('9',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('15',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( sk_A
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('30',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( sk_A
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','21','27','34','50','51','52'])).

thf('54',plain,(
    ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('56',plain,(
    ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('58',plain,(
    ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MfXXnd73Pg
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 76 iterations in 0.033s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.52  thf(t37_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.22/0.52         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.52  thf(t65_funct_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52          ( ( v2_funct_1 @ A ) =>
% 0.22/0.52            ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t65_funct_1])).
% 0.22/0.52  thf('2', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d9_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X1 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X1)
% 0.22/0.52          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('6', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf(t61_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) =>
% 0.22/0.52         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.22/0.52             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.22/0.52           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.22/0.52             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X4 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X4)
% 0.22/0.52          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.22/0.52              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.22/0.52          | ~ (v1_funct_1 @ X4)
% 0.22/0.52          | ~ (v1_relat_1 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.22/0.52          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.22/0.52         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.22/0.52  thf(t63_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52           ( ( ( v2_funct_1 @ A ) & 
% 0.22/0.52               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.22/0.52               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.22/0.52             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X5)
% 0.22/0.52          | ~ (v1_funct_1 @ X5)
% 0.22/0.52          | ((X5) = (k2_funct_1 @ X6))
% 0.22/0.52          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.22/0.52          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.22/0.52          | ~ (v2_funct_1 @ X6)
% 0.22/0.52          | ~ (v1_funct_1 @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.22/0.52          != (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.22/0.52        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.22/0.52        | ((sk_A) = (k2_funct_1 @ (k4_relat_1 @ sk_A)))
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf(dt_k2_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X2 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.52  thf('22', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X2 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.52  thf('28', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf(fc6_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.52         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X3 : $i]:
% 0.22/0.52         ((v2_funct_1 @ (k2_funct_1 @ X3))
% 0.22/0.52          | ~ (v2_funct_1 @ X3)
% 0.22/0.52          | ~ (v1_funct_1 @ X3)
% 0.22/0.52          | ~ (v1_relat_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.22/0.52  thf('35', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X3 : $i]:
% 0.22/0.52         ((v2_funct_1 @ (k2_funct_1 @ X3))
% 0.22/0.52          | ~ (v2_funct_1 @ X3)
% 0.22/0.52          | ~ (v1_funct_1 @ X3)
% 0.22/0.52          | ~ (v1_relat_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X2 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X2 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X1 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X1)
% 0.22/0.52          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52              = (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      ((((k2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.22/0.52          = (k4_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['35', '44'])).
% 0.22/0.52  thf('46', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.22/0.52  thf('51', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.22/0.52          != (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.22/0.52        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.22/0.52        | ((sk_A) = (k4_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['15', '21', '27', '34', '50', '51', '52'])).
% 0.22/0.52  thf('54', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_A)) != (sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf('56', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.22/0.52  thf('58', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.22/0.52          != (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.22/0.52        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.22/0.52          != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '59'])).
% 0.22/0.52  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.22/0.52          != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.52        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '63'])).
% 0.22/0.52  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('66', plain, (((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
