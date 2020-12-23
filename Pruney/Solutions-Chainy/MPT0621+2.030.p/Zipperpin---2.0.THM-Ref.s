%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TaEaGB5Js3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:32 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  182 (4733 expanded)
%              Number of leaves         :   27 (1552 expanded)
%              Depth                    :   38
%              Number of atoms          : 1339 (39614 expanded)
%              Number of equality atoms :  179 (5151 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

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

thf('6',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X22 = X21 )
      | ( ( k1_relat_1 @ X21 )
       != sk_A )
      | ( ( k1_relat_1 @ X22 )
       != sk_A )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('10',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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

thf('19',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('23',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_B_1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( sk_B_1 @ sk_A )
    = ( sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X19 ) @ X20 )
        = np__1 )
      | ~ ( r2_hidden @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_C @ X0 @ X1 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ X0 ) )
        = np__1 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_A
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = np__1 ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','45'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('52',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = np__1 ) ),
    inference(demod,[status(thm)],['30','48','58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = np__1 ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
    = np__1 ),
    inference(clc,[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = np__1 ) ),
    inference('sup+',[status(thm)],['17','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) )
        = np__1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('79',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('80',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('83',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
    = np__1 ),
    inference(clc,[status(thm)],['62','66'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ X0 ) )
        = np__1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('86',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( ( sk_C @ X7 @ X8 )
        = ( k1_funct_1 @ X8 @ ( sk_D @ X7 @ X8 ) ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ X0 @ X1 ) ) )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
    = np__1 ),
    inference(clc,[status(thm)],['62','66'])).

thf('94',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) ) )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('96',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('98',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ k1_xboole_0 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ sk_A @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = np__1 ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ~ ( v1_xboole_0 @ ( sk_B @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['88','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('104',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('106',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('107',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ~ ( v1_xboole_0 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( k1_xboole_0 = np__1 )
    | ~ ( v1_xboole_0 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,
    ( ( k1_xboole_0 = np__1 )
    | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('114',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( np__1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,
    ( ( np__1 = k1_xboole_0 )
    | ( k1_xboole_0 = np__1 )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( np__1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
    = np__1 ),
    inference(clc,[status(thm)],['62','66'])).

thf('120',plain,
    ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ k1_xboole_0 )
      = np__1 )
    | ( np__1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( np__1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('122',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('124',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_A )
    | ( np__1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('130',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('131',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('132',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_A )
    | ( np__1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_A )
    | ( np__1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('136',plain,
    ( ( np__1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( np__1 = k1_xboole_0 )
    | ( np__1 = k1_xboole_0 )
    | ( np__1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','136'])).

thf('138',plain,(
    np__1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    np__1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['137'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ np__1 ) @ X0 )
      | ( X0 = np__1 ) ) ),
    inference(demod,[status(thm)],['81','138','139'])).

thf('141',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = np__1 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ np__1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ~ ( v1_xboole_0 @ np__1 )
      | ( sk_A = np__1 ) ) ),
    inference('sup+',[status(thm)],['69','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('145',plain,(
    np__1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['137'])).

thf('146',plain,(
    v1_xboole_0 @ np__1 ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( sk_A = np__1 ) ) ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    np__1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['137'])).

thf('150',plain,(
    sk_A != np__1 ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['147','150'])).

thf('152',plain,(
    v1_xboole_0 @ np__1 ),
    inference(demod,[status(thm)],['144','145'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['3','151','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TaEaGB5Js3
% 0.16/0.38  % Computer   : n017.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 13:42:01 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.80/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.00  % Solved by: fo/fo7.sh
% 0.80/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.00  % done 1054 iterations in 0.524s
% 0.80/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.00  % SZS output start Refutation
% 0.80/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.00  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.80/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.80/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.80/1.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.80/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.00  thf(np__1_type, type, np__1: $i).
% 0.80/1.00  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.80/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.80/1.00  thf(sk_B_type, type, sk_B: $i > $i).
% 0.80/1.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.80/1.00  thf(l13_xboole_0, axiom,
% 0.80/1.00    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.80/1.00  thf('0', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf(t16_funct_1, conjecture,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ![B:$i]:
% 0.80/1.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.80/1.00               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.80/1.00                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.80/1.00                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.80/1.00       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i]:
% 0.80/1.00        ( ( ![B:$i]:
% 0.80/1.00            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.80/1.00              ( ![C:$i]:
% 0.80/1.00                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.80/1.00                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.80/1.00                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.80/1.00                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.80/1.00          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.80/1.00  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.80/1.00  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.80/1.00      inference('simplify', [status(thm)], ['2'])).
% 0.80/1.00  thf('4', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ?[C:$i]:
% 0.80/1.00       ( ( ![D:$i]:
% 0.80/1.00           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.80/1.00         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.80/1.00         ( v1_relat_1 @ C ) ) ))).
% 0.80/1.00  thf('5', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_1 @ X14 @ X15)) = (X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.80/1.00  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ?[B:$i]:
% 0.80/1.00       ( ( ![C:$i]:
% 0.80/1.00           ( ( r2_hidden @ C @ A ) =>
% 0.80/1.00             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.80/1.00         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.80/1.00         ( v1_relat_1 @ B ) ) ))).
% 0.80/1.00  thf('6', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      (![X21 : $i, X22 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X21)
% 0.80/1.00          | ~ (v1_funct_1 @ X21)
% 0.80/1.00          | ((X22) = (X21))
% 0.80/1.00          | ((k1_relat_1 @ X21) != (sk_A))
% 0.80/1.00          | ((k1_relat_1 @ X22) != (sk_A))
% 0.80/1.00          | ~ (v1_funct_1 @ X22)
% 0.80/1.00          | ~ (v1_relat_1 @ X22))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('8', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((X0) != (sk_A))
% 0.80/1.00          | ~ (v1_relat_1 @ X1)
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ((k1_relat_1 @ X1) != (sk_A))
% 0.80/1.00          | ((X1) = (sk_B @ X0))
% 0.80/1.00          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.80/1.00          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['6', '7'])).
% 0.80/1.00  thf('9', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('10', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('11', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((X0) != (sk_A))
% 0.80/1.00          | ~ (v1_relat_1 @ X1)
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ((k1_relat_1 @ X1) != (sk_A))
% 0.80/1.00          | ((X1) = (sk_B @ X0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.80/1.00  thf('12', plain,
% 0.80/1.00      (![X1 : $i]:
% 0.80/1.00         (((X1) = (sk_B @ sk_A))
% 0.80/1.00          | ((k1_relat_1 @ X1) != (sk_A))
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ~ (v1_relat_1 @ X1))),
% 0.80/1.00      inference('simplify', [status(thm)], ['11'])).
% 0.80/1.00  thf('13', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((X0) != (sk_A))
% 0.80/1.00          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.80/1.00          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.80/1.00          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['5', '12'])).
% 0.80/1.00  thf('14', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_1 @ X14 @ X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_1 @ X14 @ X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.80/1.00  thf('16', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.80/1.00  thf('17', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.80/1.00      inference('simplify', [status(thm)], ['16'])).
% 0.80/1.00  thf(t60_relat_1, axiom,
% 0.80/1.00    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.80/1.00     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.80/1.00  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ?[B:$i]:
% 0.80/1.00       ( ( ![C:$i]:
% 0.80/1.00           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.80/1.00         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.80/1.00         ( v1_relat_1 @ B ) ) ))).
% 0.80/1.00  thf('19', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_1 @ X19)) = (X19))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.80/1.00  thf('20', plain,
% 0.80/1.00      (![X1 : $i]:
% 0.80/1.00         (((X1) = (sk_B @ sk_A))
% 0.80/1.00          | ((k1_relat_1 @ X1) != (sk_A))
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ~ (v1_relat_1 @ X1))),
% 0.80/1.00      inference('simplify', [status(thm)], ['11'])).
% 0.80/1.00  thf('21', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((X0) != (sk_A))
% 0.80/1.00          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.80/1.00          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.80/1.00          | ((sk_B_1 @ X0) = (sk_B @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.80/1.00  thf('22', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_1 @ X19))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.80/1.00  thf('23', plain, (![X19 : $i]: (v1_funct_1 @ (sk_B_1 @ X19))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.80/1.00  thf('24', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) != (sk_A)) | ((sk_B_1 @ X0) = (sk_B @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.80/1.00  thf('25', plain, (((sk_B_1 @ sk_A) = (sk_B @ sk_A))),
% 0.80/1.00      inference('simplify', [status(thm)], ['24'])).
% 0.80/1.00  thf(d5_funct_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( r2_hidden @ C @ B ) <=>
% 0.80/1.00               ( ?[D:$i]:
% 0.80/1.00                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.80/1.00                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('26', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.80/1.00          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.80/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.80/1.00          | ~ (v1_funct_1 @ X8)
% 0.80/1.00          | ~ (v1_relat_1 @ X8))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.80/1.00  thf('27', plain,
% 0.80/1.00      (![X19 : $i, X20 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B_1 @ X19) @ X20) = (np__1))
% 0.80/1.00          | ~ (r2_hidden @ X20 @ X19))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.80/1.00  thf('28', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X1)
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ((X0) = (k2_relat_1 @ X1))
% 0.80/1.00          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.80/1.00          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_C @ X0 @ X1)) = (np__1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.00  thf('29', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ X0)) = (np__1))
% 0.80/1.00          | (r2_hidden @ (sk_D @ sk_A @ X0) @ (k1_relat_1 @ X0))
% 0.80/1.00          | ((sk_A) = (k2_relat_1 @ X0))
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ~ (v1_relat_1 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['25', '28'])).
% 0.80/1.00  thf('30', plain,
% 0.80/1.00      (((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00        | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.80/1.00        | ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['18', '29'])).
% 0.80/1.00  thf('31', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('32', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('34', plain,
% 0.80/1.00      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['32', '33'])).
% 0.80/1.00  thf('35', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf(fc8_relat_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.80/1.00       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.80/1.00  thf('36', plain,
% 0.80/1.00      (![X6 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ (k1_relat_1 @ X6))
% 0.80/1.00          | ~ (v1_relat_1 @ X6)
% 0.80/1.00          | (v1_xboole_0 @ X6))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.80/1.00  thf('37', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ X0)
% 0.80/1.00          | (v1_xboole_0 @ (sk_B @ X0))
% 0.80/1.00          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['35', '36'])).
% 0.80/1.00  thf('38', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('39', plain,
% 0.80/1.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['37', '38'])).
% 0.80/1.00  thf('40', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('41', plain,
% 0.80/1.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('42', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('43', plain,
% 0.80/1.00      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['41', '42'])).
% 0.80/1.00  thf('44', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((v1_relat_1 @ (k1_relat_1 @ X0))
% 0.80/1.00          | ~ (v1_xboole_0 @ X0)
% 0.80/1.00          | ~ (v1_xboole_0 @ X1))),
% 0.80/1.00      inference('sup+', [status(thm)], ['34', '43'])).
% 0.80/1.00  thf('45', plain,
% 0.80/1.00      (![X0 : $i]: ((v1_relat_1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('condensation', [status(thm)], ['44'])).
% 0.80/1.00  thf('46', plain,
% 0.80/1.00      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['31', '45'])).
% 0.80/1.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.80/1.00  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('50', plain,
% 0.80/1.00      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['32', '33'])).
% 0.80/1.00  thf('51', plain,
% 0.80/1.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('52', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('53', plain,
% 0.80/1.00      (![X0 : $i]: ((v1_funct_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['51', '52'])).
% 0.80/1.00  thf('54', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((v1_funct_1 @ (k1_relat_1 @ X0))
% 0.80/1.00          | ~ (v1_xboole_0 @ X0)
% 0.80/1.00          | ~ (v1_xboole_0 @ X1))),
% 0.80/1.00      inference('sup+', [status(thm)], ['50', '53'])).
% 0.80/1.00  thf('55', plain,
% 0.80/1.00      (![X0 : $i]: ((v1_funct_1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('condensation', [status(thm)], ['54'])).
% 0.80/1.00  thf('56', plain,
% 0.80/1.00      (((v1_funct_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['49', '55'])).
% 0.80/1.00  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('58', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('59', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('60', plain,
% 0.80/1.00      (((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.80/1.00        | ((sk_A) = (k1_xboole_0))
% 0.80/1.00        | ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['30', '48', '58', '59'])).
% 0.80/1.00  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('62', plain,
% 0.80/1.00      (((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.80/1.00        | ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1)))),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.80/1.00  thf(t113_zfmisc_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.80/1.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.80/1.00  thf('63', plain,
% 0.80/1.00      (![X2 : $i, X3 : $i]:
% 0.80/1.00         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.80/1.00  thf('64', plain,
% 0.80/1.00      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['63'])).
% 0.80/1.00  thf(t152_zfmisc_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.80/1.00  thf('65', plain,
% 0.80/1.00      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.80/1.00      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.80/1.00  thf('66', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/1.00      inference('sup-', [status(thm)], ['64', '65'])).
% 0.80/1.00  thf('67', plain,
% 0.80/1.00      (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1))),
% 0.80/1.00      inference('clc', [status(thm)], ['62', '66'])).
% 0.80/1.00  thf('68', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.80/1.00           = (np__1))),
% 0.80/1.00      inference('sup+', [status(thm)], ['17', '67'])).
% 0.80/1.00  thf('69', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_C_1 @ X1 @ sk_A) @ (sk_C @ sk_A @ X0)) = (np__1))
% 0.80/1.00          | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['4', '68'])).
% 0.80/1.00  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('71', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.80/1.00          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.80/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.80/1.00          | ~ (v1_funct_1 @ X8)
% 0.80/1.00          | ~ (v1_relat_1 @ X8))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.80/1.00  thf('72', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/1.00      inference('sup-', [status(thm)], ['64', '65'])).
% 0.80/1.00  thf('74', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['72', '73'])).
% 0.80/1.00  thf('75', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X0)
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ((X1) = (k2_relat_1 @ X0))
% 0.80/1.00          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.80/1.00          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['71', '74'])).
% 0.80/1.00  thf('76', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.00          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.80/1.00          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.80/1.00          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['70', '75'])).
% 0.80/1.00  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('78', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('79', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('80', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('81', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.80/1.00  thf('82', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('83', plain,
% 0.80/1.00      (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1))),
% 0.80/1.00      inference('clc', [status(thm)], ['62', '66'])).
% 0.80/1.00  thf('84', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ X0)) = (np__1))
% 0.80/1.00          | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['82', '83'])).
% 0.80/1.00  thf('85', plain,
% 0.80/1.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['37', '38'])).
% 0.80/1.00  thf('86', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.80/1.00          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.80/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.80/1.00          | ~ (v1_funct_1 @ X8)
% 0.80/1.00          | ~ (v1_relat_1 @ X8))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.80/1.00  thf('87', plain,
% 0.80/1.00      (![X17 : $i, X18 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (k1_xboole_0))
% 0.80/1.00          | ~ (r2_hidden @ X18 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('88', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X0)
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ((X1) = (k2_relat_1 @ X0))
% 0.80/1.00          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.80/1.00          | ((k1_funct_1 @ (sk_B @ (k1_relat_1 @ X0)) @ (sk_D @ X1 @ X0))
% 0.80/1.00              = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['86', '87'])).
% 0.80/1.00  thf('89', plain,
% 0.80/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.80/1.00  thf('90', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.80/1.00          | ((sk_C @ X7 @ X8) = (k1_funct_1 @ X8 @ (sk_D @ X7 @ X8)))
% 0.80/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.80/1.00          | ~ (v1_funct_1 @ X8)
% 0.80/1.00          | ~ (v1_relat_1 @ X8))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.80/1.00  thf('91', plain,
% 0.80/1.00      (![X17 : $i, X18 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (k1_xboole_0))
% 0.80/1.00          | ~ (r2_hidden @ X18 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('92', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X1)
% 0.80/1.00          | ~ (v1_funct_1 @ X1)
% 0.80/1.00          | ((X0) = (k2_relat_1 @ X1))
% 0.80/1.00          | ((sk_C @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_D @ X0 @ X1)))
% 0.80/1.00          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ X1)) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['90', '91'])).
% 0.80/1.00  thf('93', plain,
% 0.80/1.00      (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1))),
% 0.80/1.00      inference('clc', [status(thm)], ['62', '66'])).
% 0.80/1.00  thf('94', plain,
% 0.80/1.00      ((((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0)
% 0.80/1.00            = (k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0)))
% 0.80/1.00        | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.80/1.00        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['92', '93'])).
% 0.80/1.00  thf('95', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('96', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('98', plain,
% 0.80/1.00      ((((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0)
% 0.80/1.00            = (k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0)))
% 0.80/1.00        | ((sk_A) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.80/1.00  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('100', plain,
% 0.80/1.00      ((((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0)
% 0.80/1.00            = (k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))))),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 0.80/1.00  thf('101', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((sk_C @ sk_A @ k1_xboole_0)
% 0.80/1.00            = (k1_funct_1 @ X0 @ (sk_D @ sk_A @ k1_xboole_0)))
% 0.80/1.00          | ~ (v1_xboole_0 @ X0)
% 0.80/1.00          | ((k1_xboole_0) = (np__1)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['89', '100'])).
% 0.80/1.00  thf('102', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.80/1.00        | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.80/1.00        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ~ (v1_xboole_0 @ (sk_B @ (k1_relat_1 @ k1_xboole_0))))),
% 0.80/1.00      inference('sup+', [status(thm)], ['88', '101'])).
% 0.80/1.00  thf('103', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('104', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('106', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('107', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.80/1.00        | ((sk_A) = (k1_xboole_0))
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ~ (v1_xboole_0 @ (sk_B @ k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.80/1.00  thf('108', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('109', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ~ (v1_xboole_0 @ (sk_B @ k1_xboole_0)))),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.80/1.00  thf('110', plain,
% 0.80/1.00      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['85', '109'])).
% 0.80/1.00  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('112', plain,
% 0.80/1.00      ((((k1_xboole_0) = (np__1))
% 0.80/1.00        | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['110', '111'])).
% 0.80/1.00  thf('113', plain,
% 0.80/1.00      (![X17 : $i, X18 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (k1_xboole_0))
% 0.80/1.00          | ~ (r2_hidden @ X18 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('114', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.80/1.00            = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['112', '113'])).
% 0.80/1.00  thf('115', plain,
% 0.80/1.00      ((((np__1) = (k1_xboole_0))
% 0.80/1.00        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['84', '114'])).
% 0.80/1.00  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('117', plain,
% 0.80/1.00      ((((np__1) = (k1_xboole_0))
% 0.80/1.00        | ((k1_xboole_0) = (np__1))
% 0.80/1.00        | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['115', '116'])).
% 0.80/1.00  thf('118', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | ((np__1) = (k1_xboole_0)))),
% 0.80/1.00      inference('simplify', [status(thm)], ['117'])).
% 0.80/1.00  thf('119', plain,
% 0.80/1.00      (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (np__1))),
% 0.80/1.00      inference('clc', [status(thm)], ['62', '66'])).
% 0.80/1.00  thf('120', plain,
% 0.80/1.00      ((((k1_funct_1 @ (sk_B @ sk_A) @ k1_xboole_0) = (np__1))
% 0.80/1.00        | ((np__1) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['118', '119'])).
% 0.80/1.00  thf('121', plain,
% 0.80/1.00      ((((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.80/1.00        | ((np__1) = (k1_xboole_0)))),
% 0.80/1.00      inference('simplify', [status(thm)], ['117'])).
% 0.80/1.00  thf('122', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.80/1.00          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.80/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.80/1.00          | ~ (v1_funct_1 @ X8)
% 0.80/1.00          | ~ (v1_relat_1 @ X8))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.80/1.00  thf('123', plain,
% 0.80/1.00      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['32', '33'])).
% 0.80/1.00  thf('124', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/1.00      inference('sup-', [status(thm)], ['64', '65'])).
% 0.80/1.00  thf('125', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['123', '124'])).
% 0.80/1.00  thf('126', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (v1_relat_1 @ X0)
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ((X1) = (k2_relat_1 @ X0))
% 0.80/1.00          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.80/1.00          | ~ (v1_xboole_0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['122', '125'])).
% 0.80/1.00  thf('127', plain,
% 0.80/1.00      (((r2_hidden @ k1_xboole_0 @ sk_A)
% 0.80/1.00        | ((np__1) = (k1_xboole_0))
% 0.80/1.00        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.00        | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.80/1.00        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.80/1.00        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['121', '126'])).
% 0.80/1.00  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('129', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.80/1.00  thf('130', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('131', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('132', plain,
% 0.80/1.00      (((r2_hidden @ k1_xboole_0 @ sk_A)
% 0.80/1.00        | ((np__1) = (k1_xboole_0))
% 0.80/1.00        | ((sk_A) = (k1_xboole_0)))),
% 0.80/1.00      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 0.80/1.00  thf('133', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('134', plain,
% 0.80/1.00      (((r2_hidden @ k1_xboole_0 @ sk_A) | ((np__1) = (k1_xboole_0)))),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 0.80/1.00  thf('135', plain,
% 0.80/1.00      (![X17 : $i, X18 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (k1_xboole_0))
% 0.80/1.00          | ~ (r2_hidden @ X18 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.80/1.00  thf('136', plain,
% 0.80/1.00      ((((np__1) = (k1_xboole_0))
% 0.80/1.00        | ((k1_funct_1 @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['134', '135'])).
% 0.80/1.00  thf('137', plain,
% 0.80/1.00      ((((np__1) = (k1_xboole_0))
% 0.80/1.00        | ((np__1) = (k1_xboole_0))
% 0.80/1.00        | ((np__1) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['120', '136'])).
% 0.80/1.00  thf('138', plain, (((np__1) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['137'])).
% 0.80/1.00  thf('139', plain, (((np__1) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['137'])).
% 0.80/1.00  thf('140', plain,
% 0.80/1.00      (![X0 : $i]: ((r2_hidden @ (sk_C @ X0 @ np__1) @ X0) | ((X0) = (np__1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['81', '138', '139'])).
% 0.80/1.00  thf('141', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.80/1.00         (((k1_funct_1 @ (sk_C_1 @ X14 @ X15) @ X16) = (X14))
% 0.80/1.00          | ~ (r2_hidden @ X16 @ X15))),
% 0.80/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.80/1.00  thf('142', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((X0) = (np__1))
% 0.80/1.00          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ np__1)) = (X1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['140', '141'])).
% 0.80/1.00  thf('143', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((np__1) = (X0)) | ~ (v1_xboole_0 @ np__1) | ((sk_A) = (np__1)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['69', '142'])).
% 0.80/1.00  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.00  thf('145', plain, (((np__1) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['137'])).
% 0.80/1.00  thf('146', plain, ((v1_xboole_0 @ np__1)),
% 0.80/1.00      inference('demod', [status(thm)], ['144', '145'])).
% 0.80/1.00  thf('147', plain, (![X0 : $i]: (((np__1) = (X0)) | ((sk_A) = (np__1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['143', '146'])).
% 0.80/1.00  thf('148', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('149', plain, (((np__1) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['137'])).
% 0.80/1.00  thf('150', plain, (((sk_A) != (np__1))),
% 0.80/1.00      inference('demod', [status(thm)], ['148', '149'])).
% 0.80/1.00  thf('151', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['147', '150'])).
% 0.80/1.00  thf('152', plain, ((v1_xboole_0 @ np__1)),
% 0.80/1.00      inference('demod', [status(thm)], ['144', '145'])).
% 0.80/1.00  thf('153', plain, ($false),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '151', '152'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
