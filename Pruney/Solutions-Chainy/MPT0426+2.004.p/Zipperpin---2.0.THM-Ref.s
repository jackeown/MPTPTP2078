%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kioyb70ApY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 398 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  664 (4844 expanded)
%              Number of equality atoms :   54 ( 250 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(t58_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r2_hidden @ B @ A )
       => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
             => ( r2_hidden @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ C )
               => ( r2_hidden @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_3 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = ( k6_setfam_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('8',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('11',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X20 )
      | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X11
       != ( k1_setfam_1 @ X12 ) )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ X11 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('17',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r2_hidden @ X15 @ ( k1_setfam_1 @ X12 ) )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X14 @ X12 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X0 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_D_3 ) )
   <= ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_3 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_3 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D_3 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_3 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X16: $i] :
      ( ( X11
       != ( k1_setfam_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X11 )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X12 ) @ X12 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('36',plain,(
    ! [X12: $i,X16: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X12 ) @ X12 )
      | ( r2_hidden @ X16 @ ( k1_setfam_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X20 ) )
   <= ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('38',plain,
    ( ! [X20: $i] :
        ( ~ ( r2_hidden @ X20 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X20 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('39',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X20 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32','38'])).

thf('40',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_2 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X16: $i] :
      ( ( X11
       != ( k1_setfam_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X11 )
      | ~ ( r2_hidden @ X16 @ ( sk_D_2 @ X16 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('43',plain,(
    ! [X12: $i,X16: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r2_hidden @ X16 @ ( sk_D_2 @ X16 @ X12 ) )
      | ( r2_hidden @ X16 @ ( k1_setfam_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','50'])).

thf('55',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X10 @ X9 )
        = X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('57',plain,(
    ! [X10: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( ( k8_setfam_1 @ X10 @ k1_xboole_0 )
        = X10 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['52','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kioyb70ApY
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 286 iterations in 0.113s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.21/0.56  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.56  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.56  thf(t58_setfam_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ( r2_hidden @ B @ A ) =>
% 0.21/0.56         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.21/0.56           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56          ( ( r2_hidden @ B @ A ) =>
% 0.21/0.56            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.21/0.56              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ sk_D_3)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.21/0.56       ~ ((r2_hidden @ sk_B @ sk_D_3))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (((r2_hidden @ sk_D_3 @ sk_C_1)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (((r2_hidden @ sk_D_3 @ sk_C_1)) | 
% 0.21/0.56       ~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (((r2_hidden @ sk_D_3 @ sk_C_1)) <= (((r2_hidden @ sk_D_3 @ sk_C_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['3'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d10_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (((X9) = (k1_xboole_0))
% 0.21/0.56          | ((k8_setfam_1 @ X10 @ X9) = (k6_setfam_1 @ X10 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.56  thf('11', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X20 @ sk_C_1)
% 0.21/0.56          | (r2_hidden @ sk_B @ X20)
% 0.21/0.56          | (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.56         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.56         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '14'])).
% 0.21/0.56  thf(d1_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.56               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (((X11) != (k1_setfam_1 @ X12))
% 0.21/0.56          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.56          | (r2_hidden @ X15 @ X14)
% 0.21/0.56          | ~ (r2_hidden @ X15 @ X11)
% 0.21/0.56          | ((X12) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (((X12) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X15 @ (k1_setfam_1 @ X12))
% 0.21/0.56          | (r2_hidden @ X15 @ X14)
% 0.21/0.56          | ~ (r2_hidden @ X14 @ X12))),
% 0.21/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (((sk_C_1) = (k1_xboole_0))
% 0.21/0.56           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.56           | (r2_hidden @ sk_B @ X0)
% 0.21/0.56           | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.56         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((r2_hidden @ sk_B @ X0)
% 0.21/0.56           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.56           | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.56         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_D_3)))
% 0.21/0.56         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.21/0.56             ((r2_hidden @ sk_D_3 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ sk_D_3)) <= (~ ((r2_hidden @ sk_B @ sk_D_3)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((((sk_C_1) = (k1_xboole_0)))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_B @ sk_D_3)) & 
% 0.21/0.56             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.21/0.56             ((r2_hidden @ sk_D_3 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((r2_hidden @ sk_D_3 @ sk_C_1)) <= (((r2_hidden @ sk_D_3 @ sk_C_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['3'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (((r2_hidden @ sk_D_3 @ k1_xboole_0))
% 0.21/0.56         <= (~ ((r2_hidden @ sk_B @ sk_D_3)) & 
% 0.21/0.56             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.21/0.56             ((r2_hidden @ sk_D_3 @ sk_C_1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf(t1_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.56  thf('25', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.56  thf(t46_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.56  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf(d5_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.57          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.57  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.57      inference('condensation', [status(thm)], ['30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_D_3 @ sk_C_1)) | ((r2_hidden @ sk_B @ sk_D_3))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '31'])).
% 0.21/0.57  thf('33', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '32'])).
% 0.21/0.57  thf('34', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X16 : $i]:
% 0.21/0.57         (((X11) != (k1_setfam_1 @ X12))
% 0.21/0.57          | (r2_hidden @ X16 @ X11)
% 0.21/0.57          | (r2_hidden @ (sk_D_2 @ X16 @ X12) @ X12)
% 0.21/0.57          | ((X12) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X12 : $i, X16 : $i]:
% 0.21/0.57         (((X12) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ (sk_D_2 @ X16 @ X12) @ X12)
% 0.21/0.57          | (r2_hidden @ X16 @ (k1_setfam_1 @ X12)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((![X20 : $i]: (~ (r2_hidden @ X20 @ sk_C_1) | (r2_hidden @ sk_B @ X20)))
% 0.21/0.57         <= ((![X20 : $i]:
% 0.21/0.57                (~ (r2_hidden @ X20 @ sk_C_1) | (r2_hidden @ sk_B @ X20))))),
% 0.21/0.57      inference('split', [status(esa)], ['13'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((![X20 : $i]: (~ (r2_hidden @ X20 @ sk_C_1) | (r2_hidden @ sk_B @ X20))) | 
% 0.21/0.57       ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['13'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((![X20 : $i]: (~ (r2_hidden @ X20 @ sk_C_1) | (r2_hidden @ sk_B @ X20)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '32', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X20 : $i]: (~ (r2_hidden @ X20 @ sk_C_1) | (r2_hidden @ sk_B @ X20))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ sk_B @ (sk_D_2 @ X0 @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X16 : $i]:
% 0.21/0.57         (((X11) != (k1_setfam_1 @ X12))
% 0.21/0.57          | (r2_hidden @ X16 @ X11)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (sk_D_2 @ X16 @ X12))
% 0.21/0.57          | ((X12) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X12 : $i, X16 : $i]:
% 0.21/0.57         (((X12) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (sk_D_2 @ X16 @ X12))
% 0.21/0.57          | (r2_hidden @ X16 @ (k1_setfam_1 @ X12)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.57        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '43'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.57         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '32'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['48', '49'])).
% 0.21/0.57  thf('51', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['45', '50'])).
% 0.21/0.57  thf('52', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('54', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['45', '50'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (((X9) != (k1_xboole_0))
% 0.21/0.57          | ((k8_setfam_1 @ X10 @ X9) = (X10))
% 0.21/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (![X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.21/0.57          | ((k8_setfam_1 @ X10 @ k1_xboole_0) = (X10)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.57  thf('58', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.57  thf('59', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('60', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['52', '58', '59'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
