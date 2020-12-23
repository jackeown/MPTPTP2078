%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFQUWfGi59

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 179 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  622 (1654 expanded)
%              Number of equality atoms :  112 ( 299 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
        = X14 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X13 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X13 @ X14 ) )
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ~ ( r1_tarski @ sk_B_2 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_B_2
       != ( k1_relat_1 @ sk_B_2 ) ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_2 @ X0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

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

thf('30',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( sk_B_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B_1 @ sk_B_2 ) )
      | ( ( sk_B_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('36',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B_1 @ sk_B_2 ) )
      | ( ( sk_B_1 @ sk_B_2 )
        = sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('41',plain,
    ( ( v1_relat_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('44',plain,
    ( ( v1_funct_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28','41','44','49'])).

thf('51',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['13','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,
    ( ( ( sk_B_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('63',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('64',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('68',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('69',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61','66','69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFQUWfGi59
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 387 iterations in 0.140s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(t15_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ?[C:$i]:
% 0.38/0.60           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.38/0.60             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.38/0.60             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14)) | ((X14) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         ((v1_relat_1 @ (sk_C @ X13 @ X14)) | ((X14) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         ((v1_funct_1 @ (sk_C @ X13 @ X14)) | ((X14) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.38/0.60  thf(d1_xboole_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.60  thf(l1_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X6 : $i, X8 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         (((k2_relat_1 @ (sk_C @ X13 @ X14)) = (k1_tarski @ X13))
% 0.38/0.60          | ((X14) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.38/0.60  thf(t18_funct_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60          ( ![C:$i]:
% 0.38/0.60            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.60              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.38/0.60                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i]:
% 0.38/0.60        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60             ( ![C:$i]:
% 0.38/0.60               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.60                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.38/0.60                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X15 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ X15))
% 0.38/0.60          | ~ (v1_funct_1 @ X15)
% 0.38/0.60          | ~ (v1_relat_1 @ X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.38/0.60          | ((X1) = (k1_xboole_0))
% 0.38/0.60          | ~ (v1_relat_1 @ (sk_C @ X0 @ X1))
% 0.38/0.60          | ~ (v1_funct_1 @ (sk_C @ X0 @ X1))
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ X0 @ X1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.38/0.60          | ~ (v1_funct_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.38/0.60          | ((X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_xboole_0))
% 0.38/0.60          | ((X0) = (k1_xboole_0))
% 0.38/0.60          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.38/0.60          | (v1_xboole_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.38/0.60          | ((X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_xboole_0))
% 0.38/0.60          | ((X0) = (k1_xboole_0))
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.38/0.60          | (v1_xboole_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '11'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.38/0.60          | ((X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.38/0.60  thf(l13_xboole_0, axiom,
% 0.38/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.60  thf('15', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      ((![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.38/0.60         <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      ((~ (v1_xboole_0 @ sk_A)) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf(t60_relat_1, axiom,
% 0.38/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.60  thf('20', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      ((((k2_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      ((((k2_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X15 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ X15))
% 0.38/0.60          | ~ (v1_funct_1 @ X15)
% 0.38/0.60          | ~ (v1_relat_1 @ X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (((~ (r1_tarski @ sk_B_2 @ sk_A)
% 0.38/0.60         | ~ (v1_relat_1 @ sk_B_2)
% 0.38/0.60         | ~ (v1_funct_1 @ sk_B_2)
% 0.38/0.60         | ((sk_B_2) != (k1_relat_1 @ sk_B_2))))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.60  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((![X0 : $i]: (r1_tarski @ sk_B_2 @ X0))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ?[B:$i]:
% 0.38/0.60       ( ( ![C:$i]:
% 0.38/0.60           ( ( r2_hidden @ C @ A ) =>
% 0.38/0.60             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.38/0.60         ( v1_relat_1 @ B ) ) ))).
% 0.38/0.60  thf('30', plain, (![X11 : $i]: ((k1_relat_1 @ (sk_B_1 @ X11)) = (X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf(t64_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X10 : $i]:
% 0.38/0.60         (((k1_relat_1 @ X10) != (k1_xboole_0))
% 0.38/0.60          | ((X10) = (k1_xboole_0))
% 0.38/0.60          | ~ (v1_relat_1 @ X10))),
% 0.38/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) != (k1_xboole_0))
% 0.38/0.60          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.38/0.60          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.60        | ~ (v1_relat_1 @ (sk_B_1 @ k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (((~ (v1_relat_1 @ (sk_B_1 @ sk_B_2))
% 0.38/0.60         | ((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['29', '33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (((~ (v1_relat_1 @ (sk_B_1 @ sk_B_2)) | ((sk_B_1 @ sk_B_2) = (sk_B_2))))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.60  thf('38', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      ((((sk_B_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('41', plain, (((v1_relat_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      ((((sk_B_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('43', plain, (![X11 : $i]: (v1_funct_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('44', plain, (((v1_funct_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      ((((k1_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.38/0.60         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      ((((k1_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      ((((sk_B_2) != (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['25', '28', '41', '44', '49'])).
% 0.38/0.60  thf('51', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.60      inference('split', [status(esa)], ['15'])).
% 0.38/0.60  thf('53', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.38/0.60  thf('54', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['18', '53'])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k1_xboole_0))
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))))),
% 0.38/0.60      inference('clc', [status(thm)], ['13', '54'])).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((sk_B_2) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '55'])).
% 0.38/0.60  thf('57', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.60  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      (![X15 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 0.38/0.60          | ((sk_B_2) != (k1_relat_1 @ X15))
% 0.38/0.60          | ~ (v1_funct_1 @ X15)
% 0.38/0.60          | ~ (v1_relat_1 @ X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.38/0.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.38/0.60        | ((sk_B_2) != (k1_relat_1 @ k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.60  thf('61', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.60  thf('62', plain,
% 0.38/0.60      ((((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.60        | ~ (v1_relat_1 @ (sk_B_1 @ k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.60  thf('63', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('64', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.60  thf('65', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['64', '65'])).
% 0.38/0.60  thf('67', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.60  thf('68', plain, (![X11 : $i]: (v1_funct_1 @ (sk_B_1 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.60  thf('69', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['67', '68'])).
% 0.38/0.60  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.60  thf('71', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['60', '61', '66', '69', '70'])).
% 0.38/0.60  thf('72', plain, ($false),
% 0.38/0.60      inference('simplify_reflect-', [status(thm)], ['57', '71'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
