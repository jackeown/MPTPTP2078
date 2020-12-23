%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0800+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J0Xsf7K5bO

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:30 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 202 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  566 (2132 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(t52_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( ( r4_wellord1 @ A @ B )
                    & ( r4_wellord1 @ B @ C ) )
                 => ( r4_wellord1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_wellord1])).

thf('2',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( r3_wellord1 @ X1 @ X0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r3_wellord1 @ sk_B @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r3_wellord1 @ sk_B @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( r3_wellord1 @ X1 @ X0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t51_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( ( v1_relat_1 @ D )
                    & ( v1_funct_1 @ D ) )
                 => ! [E: $i] :
                      ( ( ( v1_relat_1 @ E )
                        & ( v1_funct_1 @ E ) )
                     => ( ( ( r3_wellord1 @ A @ B @ D )
                          & ( r3_wellord1 @ B @ C @ E ) )
                       => ( r3_wellord1 @ A @ C @ ( k5_relat_1 @ D @ E ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X7 @ X8 )
      | ~ ( r3_wellord1 @ X7 @ X10 @ X11 )
      | ( r3_wellord1 @ X9 @ X10 @ ( k5_relat_1 @ X8 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t51_wellord1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r3_wellord1 @ sk_A @ X0 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ~ ( r3_wellord1 @ sk_B @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r3_wellord1 @ sk_A @ X0 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ~ ( r3_wellord1 @ sk_B @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','22','28','29'])).

thf('31',plain,
    ( ( r3_wellord1 @ sk_A @ sk_C_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r3_wellord1 @ sk_A @ sk_C_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','37','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r3_wellord1 @ X1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r4_wellord1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r4_wellord1 @ sk_A @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r4_wellord1 @ sk_A @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( r4_wellord1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('55',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('56',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('57',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('58',plain,(
    ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('61',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','61'])).


%------------------------------------------------------------------------------
