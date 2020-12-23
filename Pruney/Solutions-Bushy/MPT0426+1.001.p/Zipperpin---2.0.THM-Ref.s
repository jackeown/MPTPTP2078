%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0426+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XyidYlNjbW

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:53 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 414 expanded)
%              Number of leaves         :   21 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  673 (4749 expanded)
%              Number of equality atoms :   54 ( 230 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k6_setfam_1 @ X10 @ X9 )
        = ( k1_setfam_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('8',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X1 @ X0 )
        = ( k6_setfam_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('11',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X14 )
      | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B @ ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

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
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X2 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('17',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X5 @ X3 ) ) ),
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
      | ( r2_hidden @ sk_B @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('28',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('30',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X7: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X7 @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('36',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( r2_hidden @ X7 @ ( k1_setfam_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X14 ) )
   <= ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X14 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('38',plain,
    ( ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X14 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X14 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32','38'])).

thf('40',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X14 ) ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X7: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X7 @ X2 )
      | ~ ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('43',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X3 ) )
      | ( r2_hidden @ X7 @ ( k1_setfam_1 @ X3 ) ) ) ),
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
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','52'])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','52'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30'])).

thf('63',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['54','63','64'])).


%------------------------------------------------------------------------------
