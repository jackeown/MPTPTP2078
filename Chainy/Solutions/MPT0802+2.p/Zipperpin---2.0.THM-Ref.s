%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0802+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pfZ0gGfjPC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 31.29s
% Output     : Refutation 31.29s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 561 expanded)
%              Number of leaves         :   18 ( 182 expanded)
%              Depth                    :   11
%              Number of atoms          :  596 (6121 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(sk_C_85_type,type,(
    sk_C_85: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(sk_C_72_type,type,(
    sk_C_72: $i > $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(t54_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ ( A @ ( B @ C ) ) ) )
               => ( v2_wellord1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( v2_wellord1 @ A )
                    & ( r3_wellord1 @ ( A @ ( B @ C ) ) ) )
                 => ( v2_wellord1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_wellord1])).

thf('0',plain,(
    ~ ( v2_wellord1 @ sk_B_57 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_relat_1 @ sk_B_57 ),
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

thf('2',plain,(
    ! [X3281: $i] :
      ( ~ ( v1_relat_2 @ X3281 )
      | ~ ( v8_relat_2 @ X3281 )
      | ~ ( v4_relat_2 @ X3281 )
      | ~ ( v6_relat_2 @ X3281 )
      | ~ ( v1_wellord1 @ X3281 )
      | ( v2_wellord1 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('3',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v1_wellord1 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_85 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ ( A @ B ) )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ ( A @ ( B @ C ) ) )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X3304: $i,X3305: $i,X3306: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r3_wellord1 @ ( X3305 @ ( X3304 @ X3306 ) ) )
      | ~ ( v1_funct_1 @ X3306 )
      | ~ ( v1_relat_1 @ X3306 )
      | ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) )
    | ~ ( v1_relat_1 @ sk_C_85 )
    | ~ ( v1_funct_1 @ sk_C_85 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_85 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C_85 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( r3_wellord1 @ ( X3305 @ ( X3304 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t53_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ ( A @ ( B @ C ) ) )
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

thf('17',plain,(
    ! [X3446: $i,X3447: $i,X3448: $i] :
      ( ~ ( v1_relat_1 @ X3446 )
      | ~ ( v1_wellord1 @ X3447 )
      | ( v1_wellord1 @ X3446 )
      | ~ ( r3_wellord1 @ ( X3447 @ ( X3446 @ X3448 ) ) )
      | ~ ( v1_funct_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3447 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v1_wellord1 @ sk_B_57 )
    | ~ ( v1_wellord1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('21',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( v1_relat_1 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('27',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( v1_funct_1 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v1_wellord1 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('34',plain,
    ( ( v1_wellord1 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_wellord1 @ sk_A_14 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_wellord1 @ sk_B_57 ),
    inference(demod,[status(thm)],['18','19','25','31','36','37'])).

thf('39',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['3','38'])).

thf('40',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('41',plain,(
    ! [X3446: $i,X3447: $i,X3448: $i] :
      ( ~ ( v1_relat_1 @ X3446 )
      | ~ ( v6_relat_2 @ X3447 )
      | ( v6_relat_2 @ X3446 )
      | ~ ( r3_wellord1 @ ( X3447 @ ( X3446 @ X3448 ) ) )
      | ~ ( v1_funct_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3447 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v6_relat_2 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('45',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('46',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v6_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('48',plain,
    ( ( v6_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v6_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v6_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['42','43','44','45','50','51'])).

thf('53',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('54',plain,(
    ! [X3446: $i,X3447: $i,X3448: $i] :
      ( ~ ( v1_relat_1 @ X3446 )
      | ~ ( v4_relat_2 @ X3447 )
      | ( v4_relat_2 @ X3446 )
      | ~ ( r3_wellord1 @ ( X3447 @ ( X3446 @ X3448 ) ) )
      | ~ ( v1_funct_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3447 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v4_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('58',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('59',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v4_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('61',plain,
    ( ( v4_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['55','56','57','58','63','64'])).

thf('66',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('67',plain,(
    ! [X3446: $i,X3447: $i,X3448: $i] :
      ( ~ ( v1_relat_1 @ X3446 )
      | ~ ( v8_relat_2 @ X3447 )
      | ( v8_relat_2 @ X3446 )
      | ~ ( r3_wellord1 @ ( X3447 @ ( X3446 @ X3448 ) ) )
      | ~ ( v1_funct_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3447 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v8_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('71',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('72',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v8_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('74',plain,
    ( ( v8_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v8_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v8_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['68','69','70','71','76','77'])).

thf('79',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('80',plain,(
    ! [X3446: $i,X3447: $i,X3448: $i] :
      ( ~ ( v1_relat_1 @ X3446 )
      | ~ ( v1_relat_2 @ X3447 )
      | ( v1_relat_2 @ X3446 )
      | ~ ( r3_wellord1 @ ( X3447 @ ( X3446 @ X3448 ) ) )
      | ~ ( v1_funct_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3448 )
      | ~ ( v1_relat_1 @ X3447 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v1_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('84',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('85',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v1_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('87',plain,
    ( ( v1_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['81','82','83','84','89','90'])).

thf('92',plain,(
    v2_wellord1 @ sk_B_57 ),
    inference(demod,[status(thm)],['39','52','65','78','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
