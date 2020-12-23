%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2oqtrKTZY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 155 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  645 (1354 expanded)
%              Number of equality atoms :   81 ( 170 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
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

thf('1',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

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

thf('2',plain,(
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

thf('3',plain,(
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_2 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ sk_A )
      = ( sk_B_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_2 @ X19 ) @ X20 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_2 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X10 @ X7 ) @ ( sk_D @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X3 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('31',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ( ( k7_relat_1 @ ( sk_B_2 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( sk_B_2 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k7_relat_1 @ ( sk_B_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X15: $i] :
      ( ( ( k7_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( sk_B_2 @ X0 ) @ X0 )
        = ( sk_B_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( sk_B_2 @ X0 ) @ X0 )
      = ( sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','45'])).

thf('47',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ( ( k7_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( sk_C_2 @ X2 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('55',plain,(
    ! [X15: $i] :
      ( ( ( k7_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 )
        = ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 )
      = ( sk_C_2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ k1_xboole_0 ) )
        = X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ k1_xboole_0 ) )
        = X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2oqtrKTZY
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 126 iterations in 0.066s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ?[C:$i]:
% 0.20/0.48       ( ( ![D:$i]:
% 0.20/0.48           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ?[B:$i]:
% 0.20/0.48       ( ( ![C:$i]:
% 0.20/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('1', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_2 @ X19)) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t16_funct_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ![B:$i]:
% 0.20/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ![B:$i]:
% 0.20/0.48            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.48                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.48          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X21)
% 0.20/0.48          | ~ (v1_funct_1 @ X21)
% 0.20/0.48          | ((X22) = (X21))
% 0.20/0.48          | ((k1_relat_1 @ X21) != (sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X22) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X22)
% 0.20/0.48          | ~ (v1_relat_1 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B_2 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_B_2 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, (![X19 : $i]: (v1_funct_1 @ (sk_B_2 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('5', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_2 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ((X1) = (sk_B_2 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (((X1) = (sk_B_2 @ sk_A))
% 0.20/0.48          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 0.20/0.48          | ((sk_C_2 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.48  thf('9', plain, (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (sk_A)) | ((sk_C_2 @ X1 @ X0) = (sk_B_2 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.48  thf('12', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ sk_A) = (sk_B_2 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_B_2 @ X19) @ X20) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X20 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X0)
% 0.20/0.48          | ((k1_funct_1 @ (sk_B_2 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_C_2 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (k1_xboole_0))
% 0.20/0.48          | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (sk_C_2 @ X16 @ X17) @ X18) = (X16))
% 0.20/0.48          | ~ (r2_hidden @ X18 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X0)
% 0.20/0.48          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (X0)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['16', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((k1_xboole_0) = (X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.48  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, (![X0 : $i]: (((sk_A) != (X0)) | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.48  thf(d4_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X7 : $i, X10 : $i]:
% 0.20/0.48         (((X10) = (k1_relat_1 @ X7))
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ (sk_C @ X10 @ X7) @ (sk_D @ X10 @ X7)) @ 
% 0.20/0.48             X7)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X10 @ X7) @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.20/0.48          | ((X1) = (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ X1)
% 0.20/0.48          | ((X0) = (k1_relat_1 @ X1))
% 0.20/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf(t66_xboole_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X3 : $i]: ((r1_xboole_0 @ X3 @ X3) | ((X3) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.48  thf('31', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  thf('32', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_2 @ X19)) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t95_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.48          | ((k7_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.20/0.48          | ((k7_relat_1 @ (sk_B_2 @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_2 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.48          | ((k7_relat_1 @ (sk_B_2 @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((k7_relat_1 @ (sk_B_2 @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '36'])).
% 0.20/0.48  thf('38', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_2 @ X19)) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t98_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X15 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (X15))
% 0.20/0.48          | ~ (v1_relat_1 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k7_relat_1 @ (sk_B_2 @ X0) @ X0) = (sk_B_2 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_2 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_relat_1 @ (sk_B_2 @ X0) @ X0) = (sk_B_2 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '42'])).
% 0.20/0.48  thf('44', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_2 @ X19)) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['29', '45'])).
% 0.20/0.48  thf('47', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.48          | ((k7_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0))
% 0.20/0.48          | ((k7_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.48          | ((k7_relat_1 @ (sk_C_2 @ X2 @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k7_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.48           = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (![X15 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (X15))
% 0.20/0.48          | ~ (v1_relat_1 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k7_relat_1 @ (sk_C_2 @ X1 @ X0) @ X0) = (sk_C_2 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k7_relat_1 @ (sk_C_2 @ X1 @ X0) @ X0) = (sk_C_2 @ X1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.48  thf('59', plain, (![X0 : $i]: ((sk_C_2 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['53', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X0)
% 0.20/0.48          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ k1_xboole_0 @ (sk_B @ k1_xboole_0)) = (X0))
% 0.20/0.48          | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ k1_xboole_0 @ (sk_B @ k1_xboole_0)) = (X0))
% 0.20/0.48          | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (X1))
% 0.20/0.48          | (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.48          | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ((X0) = (X1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.48  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (![X0 : $i]: (((sk_A) != (X0)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.48  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '67'])).
% 0.20/0.48  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '68'])).
% 0.20/0.48  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('71', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
