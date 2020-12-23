%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uAhKIavsQO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 (1147 expanded)
%              Number of leaves         :   23 ( 336 expanded)
%              Depth                    :   29
%              Number of atoms          :  834 (11904 expanded)
%              Number of equality atoms :  166 (1792 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k4_tarski @ ( k1_mcart_1 @ X12 ) @ ( k2_mcart_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9
       != ( k2_mcart_1 @ X9 ) )
      | ( X9
       != ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != ( k2_mcart_1 @ ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('21',plain,(
    ! [X14: $i,X16: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X14 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != X11 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != X11 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
        = X8 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','22'])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('36',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_B = sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('39',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('42',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9
       != ( k1_mcart_1 @ X9 ) )
      | ( X9
       != ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != ( k1_mcart_1 @ ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != X10 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_tarski @ X10 @ X11 )
     != X10 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('54',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','46'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('58',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_B = sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( ( sk_B = sk_C )
      | ( sk_A = sk_C )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('62',plain,
    ( ( ( sk_B = sk_C )
      | ( sk_A = sk_C )
      | ( sk_B = sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_B = sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( sk_C != k1_xboole_0 )
      | ( sk_A = sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('67',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('72',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = sk_C )
    | ( sk_B = sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['36','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( sk_B = sk_C )
    | ( sk_A = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_B = sk_C )
    | ( sk_A = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('83',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('84',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B != sk_C ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ( sk_C != sk_C )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('90',plain,(
    sk_A != sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uAhKIavsQO
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 148 iterations in 0.047s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(t26_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.49                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.21/0.49                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ~( ![C:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.49                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.21/0.49                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d2_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X2)
% 0.21/0.49          | (r2_hidden @ X1 @ X2)
% 0.21/0.49          | (v1_xboole_0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t23_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (((X12) = (k4_tarski @ (k1_mcart_1 @ X12) @ (k2_mcart_1 @ X12)))
% 0.21/0.49          | ~ (v1_relat_1 @ X13)
% 0.21/0.49          | ~ (r2_hidden @ X12 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(fc6_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(l13_xboole_0, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.21/0.49         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('14', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X3 @ X2) | (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49        | (v1_xboole_0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.21/0.49         | (v1_xboole_0 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '17'])).
% 0.21/0.49  thf(t20_mcart_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.49       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (((X9) != (k2_mcart_1 @ X9)) | ((X9) != (k4_tarski @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k4_tarski @ X10 @ X11) != (k2_mcart_1 @ (k4_tarski @ X10 @ X11)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  thf(t7_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X14 : $i, X16 : $i]: ((k2_mcart_1 @ (k4_tarski @ X14 @ X16)) = (X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('22', plain, (![X10 : $i, X11 : $i]: ((k4_tarski @ X10 @ X11) != (X11))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_C)) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['18', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.21/0.49         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '25'])).
% 0.21/0.49  thf('27', plain, (![X10 : $i, X11 : $i]: ((k4_tarski @ X10 @ X11) != (X11))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(t195_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.49               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((k2_relat_1 @ (k2_zfmisc_1 @ X7 @ X8)) = (X8))
% 0.21/0.49          | ((X8) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.49  thf(fc11_relat_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X4 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X4)) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((~ (v1_xboole_0 @ sk_C)
% 0.21/0.49         | ((sk_A) = (k1_xboole_0))
% 0.21/0.49         | ((sk_B) = (k1_xboole_0))
% 0.21/0.49         | (v1_xboole_0 @ sk_B))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_C)) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['18', '22'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((((sk_A) = (sk_C)) | ((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_B)))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49        | (v1_xboole_0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49         | (v1_xboole_0 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (((X9) != (k1_mcart_1 @ X9)) | ((X9) != (k4_tarski @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k4_tarski @ X10 @ X11) != (k1_mcart_1 @ (k4_tarski @ X10 @ X11)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]: ((k1_mcart_1 @ (k4_tarski @ X14 @ X15)) = (X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.49  thf('46', plain, (![X10 : $i, X11 : $i]: ((k4_tarski @ X10 @ X11) != (X10))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_C)) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['42', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.21/0.49         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '49'])).
% 0.21/0.49  thf('51', plain, (![X10 : $i, X11 : $i]: ((k4_tarski @ X10 @ X11) != (X10))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((~ (v1_xboole_0 @ sk_C)
% 0.21/0.49         | ((sk_A) = (k1_xboole_0))
% 0.21/0.49         | ((sk_B) = (k1_xboole_0))
% 0.21/0.49         | (v1_xboole_0 @ sk_B))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_C)) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['42', '46'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((((sk_A) = (sk_C)) | ((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_B)))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((((sk_B) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((((sk_B) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_B) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (((((sk_A) = (sk_C)) | ((sk_B) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.49  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((((sk_C) != (k1_xboole_0)) | ((sk_A) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((((sk_C) != (sk_C)) | ((sk_A) = (sk_C))))
% 0.21/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain, ((((sk_A) = (sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.49  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((((sk_C) != (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((((sk_C) != (sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('75', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      ((((sk_A) = (sk_C)) | ((sk_B) = (sk_C)) | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['36', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      ((((sk_B) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.49  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('80', plain, ((((sk_B) = (sk_C)) | ((sk_A) = (sk_C)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.21/0.49  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('82', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('83', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('84', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.21/0.49  thf('85', plain, (((sk_B) != (sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['81', '84'])).
% 0.21/0.49  thf('86', plain, ((((sk_C) != (sk_C)) | ((sk_A) = (sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['80', '85'])).
% 0.21/0.49  thf('87', plain, (((sk_A) = (sk_C))),
% 0.21/0.49      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.49  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('89', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.21/0.49  thf('90', plain, (((sk_A) != (sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.49  thf('91', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['87', '90'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
