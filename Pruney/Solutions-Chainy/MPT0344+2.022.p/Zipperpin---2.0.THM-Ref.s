%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PIONctG7vX

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 236 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  543 (1354 expanded)
%              Number of equality atoms :   70 ( 188 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( ( k1_zfmisc_1 @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( X1 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( X1 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('29',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('32',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('33',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 = sk_B_1 ) ),
    inference(demod,[status(thm)],['11','32','36','37','41'])).

thf('43',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('44',plain,
    ( ( k1_tarski @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t83_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ X18 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t83_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ X0 @ o_0_0_xboole_0 ) )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k1_tarski @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('49',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ o_0_0_xboole_0 )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k1_tarski @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( ( k3_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ o_0_0_xboole_0 )
       != ( k1_tarski @ o_0_0_xboole_0 ) )
      | ( r2_hidden @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( ( k3_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('63',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X16 @ ( k1_tarski @ X15 ) )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['59','69'])).

thf('71',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['44','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PIONctG7vX
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 64 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(t10_subset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( ![C:$i]:
% 0.20/0.49              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.20/0.49  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d2_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X20 @ X21)
% 0.20/0.49          | (r2_hidden @ X20 @ X21)
% 0.20/0.49          | (v1_xboole_0 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.49          | (r1_tarski @ X11 @ X9)
% 0.20/0.49          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X9 : $i, X11 : $i]:
% 0.20/0.49         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.49  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((r1_tarski @ sk_B_1 @ sk_A) | ((k1_zfmisc_1 @ sk_A) = (o_0_0_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.49  thf(t28_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((k1_zfmisc_1 @ sk_A) = (o_0_0_xboole_0))
% 0.20/0.49        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t7_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X1 : $i]: (((X1) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l3_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X23 @ X24)
% 0.20/0.49          | (r2_hidden @ X23 @ X25)
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((sk_B_1) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.49  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('21', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['18', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X20 @ X21)
% 0.20/0.49          | (m1_subset_1 @ X20 @ X21)
% 0.20/0.49          | (v1_xboole_0 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X1 : $i]: (((X1) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X26 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X26 @ sk_B_1) | ~ (m1_subset_1 @ X26 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((((sk_B_1) = (o_0_0_xboole_0))
% 0.20/0.49        | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('29', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('32', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf(t1_zfmisc_1, axiom,
% 0.20/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.20/0.49  thf('33', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.49  thf('34', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((k1_zfmisc_1 @ o_0_0_xboole_0) = (k1_tarski @ o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.49  thf('37', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('39', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('40', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X6 : $i]: ((k3_xboole_0 @ X6 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((k1_tarski @ o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.20/0.49        | ((o_0_0_xboole_0) = (sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '32', '36', '37', '41'])).
% 0.20/0.49  thf('43', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('44', plain, (((k1_tarski @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((k1_zfmisc_1 @ o_0_0_xboole_0) = (k1_tarski @ o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.49  thf(t83_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k1_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.49       ( k3_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         ((k1_zfmisc_1 @ (k3_xboole_0 @ X18 @ X19))
% 0.20/0.49           = (k3_xboole_0 @ (k1_zfmisc_1 @ X18) @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_zfmisc_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k1_zfmisc_1 @ (k3_xboole_0 @ X0 @ o_0_0_xboole_0))
% 0.20/0.49           = (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ (k1_tarski @ o_0_0_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X6 : $i]: ((k3_xboole_0 @ X6 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((k1_zfmisc_1 @ o_0_0_xboole_0) = (k1_tarski @ o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k1_tarski @ o_0_0_xboole_0)
% 0.20/0.49           = (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ (k1_tarski @ o_0_0_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.49  thf(l29_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.20/0.49       ( r2_hidden @ B @ A ) ))).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         ((r2_hidden @ X13 @ X14)
% 0.20/0.49          | ((k3_xboole_0 @ X14 @ (k1_tarski @ X13)) != (k1_tarski @ X13)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tarski @ o_0_0_xboole_0) != (k1_tarski @ o_0_0_xboole_0))
% 0.20/0.49          | (r2_hidden @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]: (r2_hidden @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X9 : $i, X11 : $i]:
% 0.20/0.49         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('55', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         ((r2_hidden @ X13 @ X14)
% 0.20/0.49          | ((k3_xboole_0 @ X14 @ (k1_tarski @ X13)) != (k1_tarski @ X13)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((o_0_0_xboole_0) != (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.49           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.20/0.49           = (k5_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf(t92_xboole_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('63', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.49  thf('64', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.49  thf('65', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '65'])).
% 0.20/0.49  thf(t65_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.49          | ((k4_xboole_0 @ X16 @ (k1_tarski @ X15)) != (X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.49  thf('70', plain, (![X0 : $i]: ((o_0_0_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '69'])).
% 0.20/0.49  thf('71', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '70'])).
% 0.20/0.49  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
