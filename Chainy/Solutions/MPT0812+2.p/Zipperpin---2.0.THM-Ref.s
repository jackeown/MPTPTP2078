%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0812+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sQt6HQnwPQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 32.28s
% Output     : Refutation 32.28s
% Verified   : 
% Statistics : Number of formulae       :  125 (1164 expanded)
%              Number of leaves         :   19 ( 362 expanded)
%              Depth                    :   15
%              Number of atoms          :  692 (10489 expanded)
%              Number of equality atoms :    6 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

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

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k3_wellord1_type,type,(
    k3_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_C_72_type,type,(
    sk_C_72: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(t65_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( r4_wellord1 @ ( A @ B ) )
              & ( v2_wellord1 @ A ) )
           => ( v2_wellord1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( r4_wellord1 @ ( A @ B ) )
                & ( v2_wellord1 @ A ) )
             => ( v2_wellord1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_wellord1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X3281: $i] :
      ( ~ ( v1_relat_2 @ X3281 )
      | ~ ( v8_relat_2 @ X3281 )
      | ~ ( v4_relat_2 @ X3281 )
      | ~ ( v6_relat_2 @ X3281 )
      | ~ ( v1_wellord1 @ X3281 )
      | ( v2_wellord1 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('2',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v1_wellord1 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
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

thf('4',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( r3_wellord1 @ ( X3305 @ ( X3304 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d9_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( v2_wellord1 @ A )
              & ( r4_wellord1 @ ( A @ B ) ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( C
                    = ( k3_wellord1 @ ( A @ B ) ) )
                <=> ( r3_wellord1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X3308: $i,X3309: $i,X3310: $i] :
      ( ~ ( v1_relat_1 @ X3308 )
      | ~ ( r3_wellord1 @ ( X3309 @ ( X3308 @ X3310 ) ) )
      | ( X3310
        = ( k3_wellord1 @ ( X3309 @ X3308 ) ) )
      | ~ ( v1_funct_1 @ X3310 )
      | ~ ( v1_relat_1 @ X3310 )
      | ~ ( r4_wellord1 @ ( X3309 @ X3308 ) )
      | ~ ( v2_wellord1 @ X3309 )
      | ~ ( v1_relat_1 @ X3309 ) ) ),
    inference(cnf,[status(esa)],[d9_wellord1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 )
    | ~ ( r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) )
    | ~ ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) )
      = ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( v1_relat_1 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    r4_wellord1 @ ( sk_A_14 @ sk_B_57 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X3304: $i,X3305: $i] :
      ( ~ ( v1_relat_1 @ X3304 )
      | ~ ( r4_wellord1 @ ( X3305 @ X3304 ) )
      | ( v1_funct_1 @ ( sk_C_72 @ ( X3304 @ X3305 ) ) )
      | ~ ( v1_relat_1 @ X3305 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) )
    = ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','20','26','27'])).

thf('29',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(demod,[status(thm)],['8','28'])).

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

thf('30',plain,(
    ! [X3483: $i,X3484: $i,X3485: $i] :
      ( ~ ( v1_relat_1 @ X3483 )
      | ~ ( v1_wellord1 @ X3484 )
      | ( v1_wellord1 @ X3483 )
      | ~ ( r3_wellord1 @ ( X3484 @ ( X3483 @ X3485 ) ) )
      | ~ ( v1_funct_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3484 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v1_wellord1 @ sk_B_57 )
    | ~ ( v1_wellord1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('34',plain,
    ( ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) )
    = ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','20','26','27'])).

thf('35',plain,(
    v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('37',plain,
    ( ( sk_C_72 @ ( sk_B_57 @ sk_A_14 ) )
    = ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','20','26','27'])).

thf('38',plain,(
    v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v1_wellord1 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v1_wellord1 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_wellord1 @ sk_A_14 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_wellord1 @ sk_B_57 ),
    inference(demod,[status(thm)],['31','32','35','38','43','44'])).

thf('46',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['2','45'])).

thf('47',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(demod,[status(thm)],['8','28'])).

thf('48',plain,(
    ! [X3483: $i,X3484: $i,X3485: $i] :
      ( ~ ( v1_relat_1 @ X3483 )
      | ~ ( v4_relat_2 @ X3484 )
      | ( v4_relat_2 @ X3483 )
      | ~ ( r3_wellord1 @ ( X3484 @ ( X3483 @ X3485 ) ) )
      | ~ ( v1_funct_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3484 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v4_relat_2 @ sk_B_57 )
    | ~ ( v4_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('52',plain,(
    v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('53',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v4_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('55',plain,
    ( ( v4_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['49','50','51','52','57','58'])).

thf('60',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('61',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(demod,[status(thm)],['8','28'])).

thf('62',plain,(
    ! [X3483: $i,X3484: $i,X3485: $i] :
      ( ~ ( v1_relat_1 @ X3483 )
      | ~ ( v6_relat_2 @ X3484 )
      | ( v6_relat_2 @ X3483 )
      | ~ ( r3_wellord1 @ ( X3484 @ ( X3483 @ X3485 ) ) )
      | ~ ( v1_funct_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3484 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v6_relat_2 @ sk_B_57 )
    | ~ ( v6_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('66',plain,(
    v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('67',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v6_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('69',plain,
    ( ( v6_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v6_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v6_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['63','64','65','66','71','72'])).

thf('74',plain,
    ( ( v2_wellord1 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('75',plain,(
    ~ ( v2_wellord1 @ sk_B_57 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v1_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_B_57 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(demod,[status(thm)],['8','28'])).

thf('78',plain,(
    ! [X3483: $i,X3484: $i,X3485: $i] :
      ( ~ ( v1_relat_1 @ X3483 )
      | ~ ( v8_relat_2 @ X3484 )
      | ( v8_relat_2 @ X3483 )
      | ~ ( r3_wellord1 @ ( X3484 @ ( X3483 @ X3485 ) ) )
      | ~ ( v1_funct_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3484 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v8_relat_2 @ sk_B_57 )
    | ~ ( v8_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('82',plain,(
    v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('83',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v8_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('85',plain,
    ( ( v8_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v8_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v8_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['79','80','81','82','87','88'])).

thf('90',plain,(
    ~ ( v1_relat_2 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['76','89'])).

thf('91',plain,(
    r3_wellord1 @ ( sk_A_14 @ ( sk_B_57 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(demod,[status(thm)],['8','28'])).

thf('92',plain,(
    ! [X3483: $i,X3484: $i,X3485: $i] :
      ( ~ ( v1_relat_1 @ X3483 )
      | ~ ( v1_relat_2 @ X3484 )
      | ( v1_relat_2 @ X3483 )
      | ~ ( r3_wellord1 @ ( X3484 @ ( X3483 @ X3485 ) ) )
      | ~ ( v1_funct_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3485 )
      | ~ ( v1_relat_1 @ X3484 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ~ ( v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v1_relat_2 @ sk_B_57 )
    | ~ ( v1_relat_2 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('96',plain,(
    v1_funct_1 @ ( k3_wellord1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('97',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v1_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('99',plain,
    ( ( v1_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_B_57 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_2 @ sk_B_57 ),
    inference(demod,[status(thm)],['93','94','95','96','101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['90','103'])).

%------------------------------------------------------------------------------
