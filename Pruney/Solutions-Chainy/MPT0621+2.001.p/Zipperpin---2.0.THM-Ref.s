%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MfIK1sgYfg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:28 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 353 expanded)
%              Number of leaves         :   25 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          :  612 (3586 expanded)
%              Number of equality atoms :   90 ( 503 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('0',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X31 ) @ X32 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( sk_B_3 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ( X36 = X35 )
      | ( ( k1_relat_1 @ X35 )
       != sk_A )
      | ( ( k1_relat_1 @ X36 )
       != sk_A )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('10',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_2 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_B_3 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_3 @ X0 ) )
      | ( ( sk_B_3 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( sk_B_3 @ X33 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_funct_1 @ ( sk_B_3 @ X33 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_B_3 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_B_3 @ sk_A )
    = ( sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_3 @ X33 ) @ X34 )
        = np__1 )
      | ~ ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_3 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_funct_1 @ ( sk_B_2 @ sk_A ) @ ( sk_B @ sk_A ) )
      = np__1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0 = np__1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X20 ) @ ( sk_C_1 @ X20 ) ) @ X20 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X28 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_2 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ( ( sk_C_3 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_3 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( sk_C_3 @ X1 @ sk_A )
      = ( sk_B_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = np__1 )
      | ( ( sk_C_3 @ X0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X28 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( k1_xboole_0 = np__1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( k1_xboole_0 = np__1 ) ),
    inference('sup+',[status(thm)],['1','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    k1_xboole_0 = np__1 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != np__1 ),
    inference(demod,[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( ( sk_C_3 @ X1 @ sk_A )
      = ( sk_B_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ ( sk_B_2 @ sk_A ) @ ( sk_B @ sk_A ) )
      = np__1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = np__1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X28 @ X29 ) @ X30 )
        = X28 )
      | ~ ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( np__1 = X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('58',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    k1_xboole_0 = np__1 ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( np__1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    sk_A != np__1 ),
    inference(demod,[status(thm)],['0','47'])).

thf('66',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    np__1 != np__1 ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MfIK1sgYfg
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 266 iterations in 0.188s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(np__1_type, type, np__1: $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.46/0.64  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(t16_funct_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.64               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.64                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.46/0.64                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.46/0.64       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ![B:$i]:
% 0.46/0.64            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.64                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.64                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.46/0.64                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.46/0.64          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.46/0.64  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t60_relat_1, axiom,
% 0.46/0.64    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.64     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.64  thf(d1_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ?[B:$i]:
% 0.46/0.64       ( ( ![C:$i]:
% 0.46/0.64           ( ( r2_hidden @ C @ A ) =>
% 0.46/0.64             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.64         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.46/0.64         ( v1_relat_1 @ B ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i]:
% 0.46/0.64         (((k1_funct_1 @ (sk_B_2 @ X31) @ X32) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X32 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X0)
% 0.46/0.64          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ?[B:$i]:
% 0.46/0.64       ( ( ![C:$i]:
% 0.46/0.64           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.46/0.64         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.46/0.64         ( v1_relat_1 @ B ) ) ))).
% 0.46/0.64  thf('5', plain, (![X33 : $i]: ((k1_relat_1 @ (sk_B_3 @ X33)) = (X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.46/0.64  thf('6', plain, (![X31 : $i]: ((k1_relat_1 @ (sk_B_2 @ X31)) = (X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X35)
% 0.46/0.64          | ((X36) = (X35))
% 0.46/0.64          | ((k1_relat_1 @ X35) != (sk_A))
% 0.46/0.64          | ((k1_relat_1 @ X36) != (sk_A))
% 0.46/0.64          | ~ (v1_funct_1 @ X36)
% 0.46/0.64          | ~ (v1_relat_1 @ X36))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) != (sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.64          | ((X1) = (sk_B_2 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain, (![X31 : $i]: (v1_funct_1 @ (sk_B_2 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('10', plain, (![X31 : $i]: (v1_relat_1 @ (sk_B_2 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) != (sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.64          | ((X1) = (sk_B_2 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (((X1) = (sk_B_2 @ sk_A))
% 0.46/0.64          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) != (sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ (sk_B_3 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (sk_B_3 @ X0))
% 0.46/0.64          | ((sk_B_3 @ X0) = (sk_B_2 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '12'])).
% 0.46/0.64  thf('14', plain, (![X33 : $i]: (v1_relat_1 @ (sk_B_3 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.46/0.64  thf('15', plain, (![X33 : $i]: (v1_funct_1 @ (sk_B_3 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) != (sk_A)) | ((sk_B_3 @ X0) = (sk_B_2 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.46/0.64  thf('17', plain, (((sk_B_3 @ sk_A) = (sk_B_2 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         (((k1_funct_1 @ (sk_B_3 @ X33) @ X34) = (np__1))
% 0.46/0.64          | ~ (r2_hidden @ X34 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X0)
% 0.46/0.64          | ((k1_funct_1 @ (sk_B_3 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      ((((k1_funct_1 @ (sk_B_2 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((((k1_xboole_0) = (np__1)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['4', '21'])).
% 0.46/0.64  thf('23', plain, (((v1_xboole_0 @ sk_A) | ((k1_xboole_0) = (np__1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.64  thf('24', plain, (![X31 : $i]: ((k1_relat_1 @ (sk_B_2 @ X31)) = (X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf(t56_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.46/0.64         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X20 : $i]:
% 0.46/0.64         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X20) @ (sk_C_1 @ X20)) @ X20)
% 0.46/0.64          | ((X20) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.46/0.64  thf(d4_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.46/0.64          | (r2_hidden @ X13 @ X16)
% 0.46/0.64          | ((X16) != (k1_relat_1 @ X15)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         ((r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.46/0.64      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((X0) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_B_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.46/0.64          | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '30'])).
% 0.46/0.64  thf('32', plain, (![X31 : $i]: (v1_relat_1 @ (sk_B_2 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ?[C:$i]:
% 0.46/0.64       ( ( ![D:$i]:
% 0.46/0.64           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.46/0.64         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.46/0.64         ( v1_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i]: ((k1_relat_1 @ (sk_C_3 @ X28 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (((X1) = (sk_B_2 @ sk_A))
% 0.46/0.64          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) != (sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 0.46/0.64          | ((sk_C_3 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (sk_C_3 @ X28 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i]: (v1_funct_1 @ (sk_C_3 @ X28 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X0) != (sk_A)) | ((sk_C_3 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.64  thf('40', plain, (![X1 : $i]: ((sk_C_3 @ X1 @ sk_A) = (sk_B_2 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((sk_C_3 @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (np__1)) | ((sk_C_3 @ X0 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i]: ((k1_relat_1 @ (sk_C_3 @ X28 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      ((((k1_relat_1 @ k1_xboole_0) = (sk_A)) | ((k1_xboole_0) = (np__1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain, ((((k1_xboole_0) = (sk_A)) | ((k1_xboole_0) = (np__1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '44'])).
% 0.46/0.64  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('47', plain, (((k1_xboole_0) = (np__1))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain, (((sk_A) != (np__1))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '47'])).
% 0.46/0.64  thf('49', plain, (![X1 : $i]: ((sk_C_3 @ X1 @ sk_A) = (sk_B_2 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((((k1_funct_1 @ (sk_B_2 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '20'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_funct_1 @ (sk_C_3 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.46/0.64          | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         (((k1_funct_1 @ (sk_C_3 @ X28 @ X29) @ X30) = (X28))
% 0.46/0.64          | ~ (r2_hidden @ X30 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X0)
% 0.46/0.64          | ((k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((np__1) = (X0)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['51', '54'])).
% 0.46/0.64  thf('56', plain, (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((np__1) = (X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('58', plain, (![X31 : $i]: ((k1_relat_1 @ (sk_B_2 @ X31)) = (X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i]: (((k1_relat_1 @ k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain, (((k1_xboole_0) = (np__1))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('63', plain, (![X0 : $i]: (((np__1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain, (![X0 : $i]: (((np__1) = (X0)) | ((np__1) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['56', '63'])).
% 0.46/0.64  thf('65', plain, (((sk_A) != (np__1))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '47'])).
% 0.46/0.64  thf('66', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.46/0.64  thf('67', plain, (((np__1) != (np__1))),
% 0.46/0.64      inference('demod', [status(thm)], ['48', '66'])).
% 0.46/0.64  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
