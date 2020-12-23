%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfFt7xpPId

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:38 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 544 expanded)
%              Number of leaves         :   21 ( 172 expanded)
%              Depth                    :   19
%              Number of atoms          : 1040 (8138 expanded)
%              Number of equality atoms :   81 ( 830 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t63_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ X2 )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k1_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('10',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('19',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','23','24'])).

thf('26',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = ( k8_relat_1 @ ( k1_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('29',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k1_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X5 ) @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('34',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('36',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('41',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('47',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('48',plain,(
    ! [X15: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('49',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('56',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','45','46','53','54','55','56','57','58'])).

thf('60',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('61',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('63',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('64',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('65',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('69',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('71',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('72',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('80',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X10 ) )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('81',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('86',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('88',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('89',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['84','97'])).

thf('99',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('100',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('101',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('102',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( ( k8_relat_1 @ ( k1_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','102'])).

thf('104',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('105',plain,
    ( ( k8_relat_1 @ ( k1_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','31','105','106','107'])).

thf('109',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('111',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['108','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfFt7xpPId
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.79/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.00  % Solved by: fo/fo7.sh
% 0.79/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.00  % done 733 iterations in 0.548s
% 0.79/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.00  % SZS output start Refutation
% 0.79/1.00  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.00  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.79/1.00  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.00  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/1.00  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.00  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.79/1.00  thf(t63_funct_1, conjecture,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.00           ( ( ( v2_funct_1 @ A ) & 
% 0.79/1.00               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.79/1.00               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.79/1.00             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.00    (~( ![A:$i]:
% 0.79/1.00        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.00          ( ![B:$i]:
% 0.79/1.00            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.00              ( ( ( v2_funct_1 @ A ) & 
% 0.79/1.00                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.79/1.00                  ( ( k5_relat_1 @ A @ B ) =
% 0.79/1.00                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.79/1.00                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.79/1.00    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.79/1.00  thf('0', plain,
% 0.79/1.00      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(t123_relat_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( v1_relat_1 @ B ) =>
% 0.79/1.00       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.79/1.00  thf('1', plain,
% 0.79/1.00      (![X2 : $i, X3 : $i]:
% 0.79/1.00         (((k8_relat_1 @ X3 @ X2) = (k5_relat_1 @ X2 @ (k6_relat_1 @ X3)))
% 0.79/1.00          | ~ (v1_relat_1 @ X2))),
% 0.79/1.00      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.79/1.00  thf('2', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         (((k8_relat_1 @ (k1_relat_1 @ sk_A) @ X0)
% 0.79/1.00            = (k5_relat_1 @ X0 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.79/1.00          | ~ (v1_relat_1 @ X0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['0', '1'])).
% 0.79/1.00  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf(d9_funct_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.00       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.79/1.00  thf('4', plain,
% 0.79/1.00      (![X12 : $i]:
% 0.79/1.00         (~ (v2_funct_1 @ X12)
% 0.79/1.00          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.79/1.00          | ~ (v1_funct_1 @ X12)
% 0.79/1.00          | ~ (v1_relat_1 @ X12))),
% 0.79/1.00      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.79/1.00  thf('5', plain,
% 0.79/1.00      ((~ (v1_funct_1 @ sk_A)
% 0.79/1.00        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.79/1.00        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('6', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('7', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('8', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf(t61_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_1 @ A ) =>
% 0.79/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.79/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.79/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.79/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('9', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('10', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.79/1.01          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['8', '9'])).
% 0.79/1.01  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('14', plain,
% 0.79/1.01      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.79/1.01         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.79/1.01  thf(t55_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( v1_relat_1 @ B ) =>
% 0.79/1.01           ( ![C:$i]:
% 0.79/1.01             ( ( v1_relat_1 @ C ) =>
% 0.79/1.01               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.79/1.01                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.79/1.01  thf('15', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.79/1.01              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.79/1.01          | ~ (v1_relat_1 @ X9)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.79/1.01  thf('16', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.79/1.01            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['14', '15'])).
% 0.79/1.01  thf('17', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf(fc6_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.79/1.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.79/1.01         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.79/1.01  thf('18', plain,
% 0.79/1.01      (![X15 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.79/1.01  thf('19', plain,
% 0.79/1.01      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('22', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('23', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('25', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ X0)
% 0.79/1.01            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '23', '24'])).
% 0.79/1.01  thf('26', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)
% 0.79/1.01          = (k8_relat_1 @ (k1_relat_1 @ sk_A) @ (k4_relat_1 @ sk_A)))
% 0.79/1.01        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['2', '25'])).
% 0.79/1.01  thf('27', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t78_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ A ) =>
% 0.79/1.01       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.79/1.01  thf('28', plain,
% 0.79/1.01      (![X11 : $i]:
% 0.79/1.01         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 0.79/1.01          | ~ (v1_relat_1 @ X11))),
% 0.79/1.01      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.79/1.01  thf('29', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B) = (sk_B))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['27', '28'])).
% 0.79/1.01  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('31', plain,
% 0.79/1.01      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B) = (sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['29', '30'])).
% 0.79/1.01  thf('32', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k8_relat_1 @ (k1_relat_1 @ sk_A) @ X0)
% 0.79/1.01            = (k5_relat_1 @ X0 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['0', '1'])).
% 0.79/1.01  thf(t54_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( v1_relat_1 @ B ) =>
% 0.79/1.01           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.79/1.01             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('33', plain,
% 0.79/1.01      (![X5 : $i, X6 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X5)
% 0.79/1.01          | ((k4_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.79/1.01              = (k5_relat_1 @ (k4_relat_1 @ X5) @ (k4_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.79/1.01  thf('34', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('35', plain,
% 0.79/1.01      (![X15 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      (![X12 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X12)
% 0.79/1.01          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.79/1.01          | ~ (v1_funct_1 @ X12)
% 0.79/1.01          | ~ (v1_relat_1 @ X12))),
% 0.79/1.01      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.79/1.01              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.79/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['35', '36'])).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.79/1.01        | ((k2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.79/1.01            = (k4_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['34', '37'])).
% 0.79/1.01  thf('39', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('40', plain,
% 0.79/1.01      (![X15 : $i]:
% 0.79/1.01         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.79/1.01  thf('41', plain,
% 0.79/1.01      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['39', '40'])).
% 0.79/1.01  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('44', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('45', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.79/1.01  thf('46', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('47', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('48', plain,
% 0.79/1.01      (![X15 : $i]:
% 0.79/1.01         ((v2_funct_1 @ (k2_funct_1 @ X15))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.79/1.01  thf('49', plain,
% 0.79/1.01      (((v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['47', '48'])).
% 0.79/1.01  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('51', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('52', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('53', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.79/1.01  thf('54', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('55', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('56', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('57', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('59', plain,
% 0.79/1.01      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['38', '45', '46', '53', '54', '55', '56', '57', '58'])).
% 0.79/1.01  thf('60', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('61', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.79/1.01          = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.79/1.01        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.79/1.01  thf('62', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('63', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.79/1.01  thf('64', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.79/1.01  thf('65', plain,
% 0.79/1.01      (((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.79/1.01         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.79/1.01  thf('66', plain,
% 0.79/1.01      ((((k4_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.79/1.01          = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['33', '65'])).
% 0.79/1.01  thf('67', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('68', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('69', plain,
% 0.79/1.01      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.79/1.01         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.79/1.01  thf('70', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('71', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 0.79/1.01              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('72', plain,
% 0.79/1.01      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.79/1.01          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_A))),
% 0.79/1.01      inference('sup+', [status(thm)], ['70', '71'])).
% 0.79/1.01  thf('73', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('75', plain, ((v1_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('76', plain, ((v2_funct_1 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('77', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)) = (k5_relat_1 @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.79/1.01  thf('78', plain,
% 0.79/1.01      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['69', '77'])).
% 0.79/1.01  thf('79', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t72_relat_1, axiom,
% 0.79/1.01    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.79/1.01  thf('80', plain,
% 0.79/1.01      (![X10 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 0.79/1.01      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.79/1.01  thf('81', plain,
% 0.79/1.01      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['79', '80'])).
% 0.79/1.01  thf('82', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('83', plain,
% 0.79/1.01      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['81', '82'])).
% 0.79/1.01  thf('84', plain,
% 0.79/1.01      (((k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.79/1.01         = (k5_relat_1 @ sk_A @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['78', '83'])).
% 0.79/1.01  thf('85', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('86', plain,
% 0.79/1.01      (![X15 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.79/1.01  thf('87', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.79/1.01              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.79/1.01          | ~ (v1_relat_1 @ X9)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.79/1.01  thf('88', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 0.79/1.01              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('89', plain,
% 0.79/1.01      (![X11 : $i]:
% 0.79/1.01         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 0.79/1.01          | ~ (v1_relat_1 @ X11))),
% 0.79/1.01      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.79/1.01  thf('90', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0) = (X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['88', '89'])).
% 0.79/1.01  thf('91', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0) = (X0)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['90'])).
% 0.79/1.01  thf('92', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['87', '91'])).
% 0.79/1.01  thf('93', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['92'])).
% 0.79/1.01  thf('94', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['86', '93'])).
% 0.79/1.01  thf('95', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)) = (X0))
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['94'])).
% 0.79/1.01  thf('96', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['85', '95'])).
% 0.79/1.01  thf('97', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['96'])).
% 0.79/1.01  thf('98', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.79/1.01          = (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['84', '97'])).
% 0.79/1.01  thf('99', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('100', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.79/1.01  thf('101', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.79/1.01  thf('102', plain,
% 0.79/1.01      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.79/1.01         = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.79/1.01  thf('103', plain,
% 0.79/1.01      ((((k8_relat_1 @ (k1_relat_1 @ sk_A) @ (k4_relat_1 @ sk_A))
% 0.79/1.01          = (k4_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['32', '102'])).
% 0.79/1.01  thf('104', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('105', plain,
% 0.79/1.01      (((k8_relat_1 @ (k1_relat_1 @ sk_A) @ (k4_relat_1 @ sk_A))
% 0.79/1.01         = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['103', '104'])).
% 0.79/1.01  thf('106', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.79/1.01  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('108', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '31', '105', '106', '107'])).
% 0.79/1.01  thf('109', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('110', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('111', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['109', '110'])).
% 0.79/1.01  thf('112', plain, ($false),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['108', '111'])).
% 0.79/1.01  
% 0.79/1.01  % SZS output end Refutation
% 0.79/1.01  
% 0.79/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
