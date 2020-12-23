%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0700+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6myDQwn36d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 16.14s
% Output     : Refutation 16.14s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 130 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 (1163 expanded)
%              Number of equality atoms :   21 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(sk_B_26_type,type,(
    sk_B_26: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t155_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ ( B @ A ) )
          = ( k9_relat_1 @ ( k2_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( ( k10_relat_1 @ ( B @ A ) )
            = ( k9_relat_1 @ ( k2_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_funct_1])).

thf('0',plain,(
    ( k10_relat_1 @ ( sk_B_26 @ sk_A_8 ) )
 != ( k9_relat_1 @ ( k2_funct_1 @ sk_B_26 @ sk_A_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_relat_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X2651: $i] :
      ( ~ ( v2_funct_1 @ X2651 )
      | ( ( k2_funct_1 @ X2651 )
        = ( k4_relat_1 @ X2651 ) )
      | ~ ( v1_funct_1 @ X2651 )
      | ~ ( v1_relat_1 @ X2651 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_26 )
    | ( ( k2_funct_1 @ sk_B_26 )
      = ( k4_relat_1 @ sk_B_26 ) )
    | ~ ( v2_funct_1 @ sk_B_26 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_funct_1 @ sk_B_26 )
    = ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ ( sk_B_26 @ sk_A_8 ) )
 != ( k9_relat_1 @ ( k4_relat_1 @ sk_B_26 @ sk_A_8 ) ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k2_funct_1 @ sk_B_26 )
    = ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X2923: $i] :
      ( ~ ( v2_funct_1 @ X2923 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2923 ) )
        = X2923 )
      | ~ ( v1_funct_1 @ X2923 )
      | ~ ( v1_relat_1 @ X2923 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('10',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B_26 ) )
      = sk_B_26 )
    | ~ ( v1_relat_1 @ sk_B_26 )
    | ~ ( v1_funct_1 @ sk_B_26 )
    | ~ ( v2_funct_1 @ sk_B_26 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B_26 ) )
    = sk_B_26 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ ( B @ A ) )
          = ( k10_relat_1 @ ( k2_funct_1 @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X2801: $i,X2802: $i] :
      ( ~ ( v2_funct_1 @ X2801 )
      | ( ( k9_relat_1 @ ( X2801 @ X2802 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X2801 @ X2802 ) ) )
      | ~ ( v1_funct_1 @ X2801 )
      | ~ ( v1_relat_1 @ X2801 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B_26 @ X0 ) )
        = ( k10_relat_1 @ ( sk_B_26 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B_26 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B_26 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B_26 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_funct_1 @ sk_B_26 )
    = ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X2652: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2652 ) )
      | ~ ( v1_funct_1 @ X2652 )
      | ~ ( v1_relat_1 @ X2652 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_B_26 ) )
    | ~ ( v1_relat_1 @ sk_B_26 )
    | ~ ( v1_funct_1 @ sk_B_26 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k2_funct_1 @ sk_B_26 )
    = ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('24',plain,(
    ! [X2652: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2652 ) )
      | ~ ( v1_funct_1 @ X2652 )
      | ~ ( v1_relat_1 @ X2652 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_B_26 ) )
    | ~ ( v1_relat_1 @ sk_B_26 )
    | ~ ( v1_funct_1 @ sk_B_26 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k2_funct_1 @ sk_B_26 )
    = ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X2674: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2674 ) )
      | ~ ( v2_funct_1 @ X2674 )
      | ~ ( v1_funct_1 @ X2674 )
      | ~ ( v1_relat_1 @ X2674 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('31',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_B_26 ) )
    | ~ ( v1_relat_1 @ sk_B_26 )
    | ~ ( v1_funct_1 @ sk_B_26 )
    | ~ ( v2_funct_1 @ sk_B_26 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_B_26 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B_26 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B_26 @ X0 ) )
      = ( k10_relat_1 @ ( sk_B_26 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','28','35'])).

thf('37',plain,(
    ( k10_relat_1 @ ( sk_B_26 @ sk_A_8 ) )
 != ( k10_relat_1 @ ( sk_B_26 @ sk_A_8 ) ) ),
    inference(demod,[status(thm)],['7','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
