%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0650+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NHuwmtmiLf

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 16.50s
% Output     : Refutation 16.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 333 expanded)
%              Number of leaves         :   22 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  731 (5150 expanded)
%              Number of equality atoms :   49 ( 382 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_50_type,type,(
    sk_D_50: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_24_type,type,(
    sk_B_24: $i )).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ ( A @ ( k2_relat_1 @ B ) ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( B @ ( k1_funct_1 @ ( k2_funct_1 @ B @ A ) ) ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ ( A @ ( k2_relat_1 @ B ) ) ) )
         => ( ( A
              = ( k1_funct_1 @ ( B @ ( k1_funct_1 @ ( k2_funct_1 @ B @ A ) ) ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_8 @ ( k2_relat_1 @ sk_B_24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ ( A @ D ) ) )
                  & ( r2_hidden @ ( D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X2623: $i,X2625: $i,X2626: $i] :
      ( ( X2625
       != ( k2_relat_1 @ X2623 ) )
      | ( r2_hidden @ ( sk_D_50 @ ( X2626 @ X2623 ) @ ( k1_relat_1 @ X2623 ) ) )
      | ~ ( r2_hidden @ ( X2626 @ X2625 ) )
      | ~ ( v1_funct_1 @ X2623 )
      | ~ ( v1_relat_1 @ X2623 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X2623: $i,X2626: $i] :
      ( ~ ( v1_relat_1 @ X2623 )
      | ~ ( v1_funct_1 @ X2623 )
      | ~ ( r2_hidden @ ( X2626 @ ( k2_relat_1 @ X2623 ) ) )
      | ( r2_hidden @ ( sk_D_50 @ ( X2626 @ X2623 ) @ ( k1_relat_1 @ X2623 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) @ ( k1_relat_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) @ ( k1_relat_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B @ ( k1_funct_1 @ ( B @ A ) ) ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X2808: $i,X2809: $i] :
      ( ~ ( v2_funct_1 @ X2808 )
      | ~ ( r2_hidden @ ( X2809 @ ( k1_relat_1 @ X2808 ) ) )
      | ( X2809
        = ( k1_funct_1 @ ( k2_funct_1 @ X2808 @ ( k1_funct_1 @ ( X2808 @ X2809 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2808 )
      | ~ ( v1_relat_1 @ X2808 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ( ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ ( k1_funct_1 @ ( sk_B_24 @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) ) ) ) ) ) )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_A_8 @ ( k2_relat_1 @ sk_B_24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X2623: $i,X2625: $i,X2626: $i] :
      ( ( X2625
       != ( k2_relat_1 @ X2623 ) )
      | ( X2626
        = ( k1_funct_1 @ ( X2623 @ ( sk_D_50 @ ( X2626 @ X2623 ) ) ) ) )
      | ~ ( r2_hidden @ ( X2626 @ X2625 ) )
      | ~ ( v1_funct_1 @ X2623 )
      | ~ ( v1_relat_1 @ X2623 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X2623: $i,X2626: $i] :
      ( ~ ( v1_relat_1 @ X2623 )
      | ~ ( v1_funct_1 @ X2623 )
      | ~ ( r2_hidden @ ( X2626 @ ( k2_relat_1 @ X2623 ) ) )
      | ( X2626
        = ( k1_funct_1 @ ( X2623 @ ( sk_D_50 @ ( X2626 @ X2623 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A_8
      = ( k1_funct_1 @ ( sk_B_24 @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A_8
    = ( k1_funct_1 @ ( sk_B_24 @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ),
    inference(demod,[status(thm)],['9','10','11','18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) @ ( k1_relat_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['6','20'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ ( k5_relat_1 @ ( C @ B ) ) ) ) )
          <=> ( ( r2_hidden @ ( A @ ( k1_relat_1 @ C ) ) )
              & ( r2_hidden @ ( k1_funct_1 @ ( C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X2733: $i,X2734: $i,X2735: $i] :
      ( ~ ( v1_relat_1 @ X2733 )
      | ~ ( v1_funct_1 @ X2733 )
      | ~ ( r2_hidden @ ( X2734 @ ( k1_relat_1 @ X2733 ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( X2733 @ X2734 ) @ ( k1_relat_1 @ X2735 ) ) )
      | ( r2_hidden @ ( X2734 @ ( k1_relat_1 @ ( k5_relat_1 @ ( X2733 @ X2735 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2735 )
      | ~ ( v1_relat_1 @ X2735 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ( r2_hidden @ ( sk_A_8 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) ) ) ) )
    | ~ ( r2_hidden @ ( sk_A_8 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X2632: $i] :
      ( ~ ( v2_funct_1 @ X2632 )
      | ( ( k2_funct_1 @ X2632 )
        = ( k4_relat_1 @ X2632 ) )
      | ~ ( v1_funct_1 @ X2632 )
      | ~ ( v1_relat_1 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_B_24 )
    | ( ( k2_funct_1 @ sk_B_24 )
      = ( k4_relat_1 @ sk_B_24 ) )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X2515: $i] :
      ( ( ( k2_relat_1 @ X2515 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2515 ) ) )
      | ~ ( v1_relat_1 @ X2515 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_B_24 )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_B_24 )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_A_8 @ ( k2_relat_1 @ sk_B_24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X2652: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X2652 ) )
      | ~ ( v2_funct_1 @ X2652 )
      | ~ ( v1_funct_1 @ X2652 )
      | ~ ( v1_relat_1 @ X2652 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('39',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X2132: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2132 ) )
      | ~ ( v1_relat_1 @ X2132 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('46',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( sk_A_8 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','35','36','43','48'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ ( k5_relat_1 @ ( C @ B ) ) ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ ( C @ B ) @ A ) )
              = ( k1_funct_1 @ ( B @ ( k1_funct_1 @ ( C @ A ) ) ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X2736: $i,X2737: $i,X2738: $i] :
      ( ~ ( v1_relat_1 @ X2736 )
      | ~ ( v1_funct_1 @ X2736 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( X2736 @ X2737 ) @ X2738 ) )
        = ( k1_funct_1 @ ( X2737 @ ( k1_funct_1 @ ( X2736 @ X2738 ) ) ) ) )
      | ~ ( r2_hidden @ ( X2738 @ ( k1_relat_1 @ ( k5_relat_1 @ ( X2736 @ X2737 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2737 )
      | ~ ( v1_relat_1 @ X2737 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) )
      = ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A_8
    = ( k1_funct_1 @ ( sk_B_24 @ ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('55',plain,
    ( ( sk_D_50 @ ( sk_A_8 @ sk_B_24 ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ),
    inference(demod,[status(thm)],['9','10','11','18','19'])).

thf('56',plain,
    ( sk_A_8
    = ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('58',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('59',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) )
    = sk_A_8 ),
    inference(demod,[status(thm)],['51','52','53','56','57','58'])).

thf('60',plain,
    ( ( sk_A_8
     != ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) )
    | ( sk_A_8
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_A_8
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) )
   <= ( sk_A_8
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( sk_A_8
    = ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('63',plain,
    ( ( sk_A_8
     != ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) )
   <= ( sk_A_8
     != ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('64',plain,
    ( ( sk_A_8 != sk_A_8 )
   <= ( sk_A_8
     != ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A_8
    = ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A_8
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) )
    | ( sk_A_8
     != ( k1_funct_1 @ ( sk_B_24 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B_24 @ sk_A_8 ) ) ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('67',plain,(
    sk_A_8
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A_8
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_24 @ sk_B_24 ) @ sk_A_8 ) ) ),
    inference(simpl_trail,[status(thm)],['61','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','68'])).

%------------------------------------------------------------------------------
