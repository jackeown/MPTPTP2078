%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FJT62cUlOJ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 323 expanded)
%              Number of leaves         :   17 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  566 (2754 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(t65_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( r4_wellord1 @ A @ B )
              & ( v2_wellord1 @ A ) )
           => ( v2_wellord1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( r4_wellord1 @ A @ B )
                & ( v2_wellord1 @ A ) )
             => ( v2_wellord1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_wellord1])).

thf('0',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('2',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ A @ B @ C )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r4_wellord1 @ X2 @ X1 )
      | ( r3_wellord1 @ X2 @ X1 @ ( sk_C @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t53_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ( ( ( v1_relat_2 @ A )
                   => ( v1_relat_2 @ B ) )
                  & ( ( v8_relat_2 @ A )
                   => ( v8_relat_2 @ B ) )
                  & ( ( v6_relat_2 @ A )
                   => ( v6_relat_2 @ B ) )
                  & ( ( v4_relat_2 @ A )
                   => ( v4_relat_2 @ B ) )
                  & ( ( v1_wellord1 @ A )
                   => ( v1_wellord1 @ B ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_wellord1 @ X5 )
      | ( v1_wellord1 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r4_wellord1 @ X2 @ X1 )
      | ( v1_relat_1 @ ( sk_C @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r4_wellord1 @ X2 @ X1 )
      | ( v1_funct_1 @ ( sk_C @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('26',plain,
    ( ( v1_wellord1 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_wellord1 @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_wellord1 @ sk_B ),
    inference(demod,[status(thm)],['10','11','17','23','28','29'])).

thf('31',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['2','30'])).

thf('32',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v4_relat_2 @ X5 )
      | ( v4_relat_2 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('37',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('40',plain,
    ( ( v4_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['34','35','36','37','42','43'])).

thf('45',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v6_relat_2 @ X5 )
      | ( v6_relat_2 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v6_relat_2 @ sk_B )
    | ~ ( v6_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('51',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('54',plain,
    ( ( v6_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v6_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v6_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['48','49','50','51','56','57'])).

thf('59',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,(
    ~ ( v2_wellord1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v1_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('63',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v8_relat_2 @ X5 )
      | ( v8_relat_2 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v8_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('67',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('70',plain,
    ( ( v8_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v8_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v8_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66','67','72','73'])).

thf('75',plain,(
    ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('77',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_2 @ X5 )
      | ( v1_relat_2 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('81',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('84',plain,
    ( ( v1_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['78','79','80','81','86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['75','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FJT62cUlOJ
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:38:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 48 iterations in 0.022s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.52  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.52  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.52  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.21/0.52  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.21/0.52  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.21/0.52  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.21/0.52  thf(t65_wellord1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( ( r4_wellord1 @ A @ B ) & ( v2_wellord1 @ A ) ) =>
% 0.21/0.52             ( v2_wellord1 @ B ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( v1_relat_1 @ B ) =>
% 0.21/0.52              ( ( ( r4_wellord1 @ A @ B ) & ( v2_wellord1 @ A ) ) =>
% 0.21/0.52                ( v2_wellord1 @ B ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t65_wellord1])).
% 0.21/0.52  thf('0', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d4_wellord1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( v2_wellord1 @ A ) <=>
% 0.21/0.52         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.21/0.52           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_2 @ X0)
% 0.21/0.52          | ~ (v8_relat_2 @ X0)
% 0.21/0.52          | ~ (v4_relat_2 @ X0)
% 0.21/0.52          | ~ (v6_relat_2 @ X0)
% 0.21/0.52          | ~ (v1_wellord1 @ X0)
% 0.21/0.52          | (v2_wellord1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((v2_wellord1 @ sk_B)
% 0.21/0.52        | ~ (v1_wellord1 @ sk_B)
% 0.21/0.52        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v4_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d8_wellord1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( r4_wellord1 @ A @ B ) <=>
% 0.21/0.52             ( ?[C:$i]:
% 0.21/0.52               ( ( r3_wellord1 @ A @ B @ C ) & ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (r4_wellord1 @ X2 @ X1)
% 0.21/0.52          | (r3_wellord1 @ X2 @ X1 @ (sk_C @ X1 @ X2))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | (r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf(t53_wellord1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.21/0.52                 ( ( ( v1_relat_2 @ A ) => ( v1_relat_2 @ B ) ) & 
% 0.21/0.52                   ( ( v8_relat_2 @ A ) => ( v8_relat_2 @ B ) ) & 
% 0.21/0.52                   ( ( v6_relat_2 @ A ) => ( v6_relat_2 @ B ) ) & 
% 0.21/0.52                   ( ( v4_relat_2 @ A ) => ( v4_relat_2 @ B ) ) & 
% 0.21/0.52                   ( ( v1_wellord1 @ A ) => ( v1_wellord1 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v1_wellord1 @ X5)
% 0.21/0.52          | (v1_wellord1 @ X4)
% 0.21/0.52          | ~ (r3_wellord1 @ X5 @ X4 @ X6)
% 0.21/0.52          | ~ (v1_funct_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | (v1_wellord1 @ sk_B)
% 0.21/0.52        | ~ (v1_wellord1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (r4_wellord1 @ X2 @ X1)
% 0.21/0.52          | (v1_relat_1 @ (sk_C @ X1 @ X2))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('18', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (r4_wellord1 @ X2 @ X1)
% 0.21/0.52          | (v1_funct_1 @ (sk_C @ X1 @ X2))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_wellord1 @ X0) | (v1_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('26', plain, (((v1_wellord1 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, ((v1_wellord1 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v1_wellord1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '17', '23', '28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((v2_wellord1 @ sk_B)
% 0.21/0.52        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v4_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '30'])).
% 0.21/0.52  thf('32', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v4_relat_2 @ X5)
% 0.21/0.52          | (v4_relat_2 @ X4)
% 0.21/0.52          | ~ (r3_wellord1 @ X5 @ X4 @ X6)
% 0.21/0.52          | ~ (v1_funct_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | (v4_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v4_relat_2 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('37', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_wellord1 @ X0) | (v4_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('40', plain, (((v4_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v4_relat_2 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain, ((v4_relat_2 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['34', '35', '36', '37', '42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v2_wellord1 @ sk_B)
% 0.21/0.52        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '44'])).
% 0.21/0.52  thf('46', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v6_relat_2 @ X5)
% 0.21/0.52          | (v6_relat_2 @ X4)
% 0.21/0.52          | ~ (r3_wellord1 @ X5 @ X4 @ X6)
% 0.21/0.52          | ~ (v1_funct_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | (v6_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v6_relat_2 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('50', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('51', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_wellord1 @ X0) | (v6_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('54', plain, (((v6_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, ((v6_relat_2 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('58', plain, ((v6_relat_2 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['48', '49', '50', '51', '56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((v2_wellord1 @ sk_B) | ~ (v8_relat_2 @ sk_B) | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '58'])).
% 0.21/0.52  thf('60', plain, (~ (v2_wellord1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((~ (v1_relat_2 @ sk_B) | ~ (v8_relat_2 @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v8_relat_2 @ X5)
% 0.21/0.52          | (v8_relat_2 @ X4)
% 0.21/0.52          | ~ (r3_wellord1 @ X5 @ X4 @ X6)
% 0.21/0.52          | ~ (v1_funct_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | (v8_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v8_relat_2 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('67', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_wellord1 @ X0) | (v8_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('70', plain, (((v8_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain, ((v8_relat_2 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67', '72', '73'])).
% 0.21/0.52  thf('75', plain, (~ (v1_relat_2 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['61', '74'])).
% 0.21/0.52  thf('76', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v1_relat_2 @ X5)
% 0.21/0.52          | (v1_relat_2 @ X4)
% 0.21/0.52          | ~ (r3_wellord1 @ X5 @ X4 @ X6)
% 0.21/0.52          | ~ (v1_funct_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52        | (v1_relat_2 @ sk_B)
% 0.21/0.52        | ~ (v1_relat_2 @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('81', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.52  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_wellord1 @ X0) | (v1_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.52  thf('84', plain, (((v1_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('86', plain, ((v1_relat_2 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.52  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('88', plain, ((v1_relat_2 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['78', '79', '80', '81', '86', '87'])).
% 0.21/0.52  thf('89', plain, ($false), inference('demod', [status(thm)], ['75', '88'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
