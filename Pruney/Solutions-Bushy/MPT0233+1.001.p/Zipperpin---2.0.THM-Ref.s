%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0233+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y4TEjyJ8GI

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:33 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 220 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   26
%              Number of atoms          :  759 (2517 expanded)
%              Number of equality atoms :  149 ( 482 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X5 ) )
      | ( X4
       != ( k2_tarski @ X2 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('1',plain,(
    ! [X2: $i,X5: $i] :
      ( r1_tarski @ ( k2_tarski @ X2 @ X5 ) @ ( k2_tarski @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k2_tarski @ X2 @ X3 ) )
      | ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4
        = ( k1_tarski @ X2 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k2_tarski @ X2 @ X3 ) )
      | ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4
        = ( k1_tarski @ X2 ) )
      | ( X4 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k2_tarski @ X2 @ X3 ) )
      | ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4
        = ( k1_tarski @ X2 ) )
      | ( X4 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_C ) )
      | ( X0
        = ( k1_tarski @ sk_D ) )
      | ( X0
        = ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t10_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( ( k2_tarski @ A @ B )
          = ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ( X7 = X8 )
      | ( ( k2_tarski @ X7 @ X9 )
       != ( k2_tarski @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = o_0_0_xboole_0 )
      | ( sk_C = X0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_C = sk_A )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['13'])).

thf('15',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 = X10 )
      | ( ( k1_tarski @ X11 )
       != ( k2_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = o_0_0_xboole_0 )
      | ( sk_C = sk_B )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_D = sk_A )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 = X10 )
      | ( ( k1_tarski @ X11 )
       != ( k2_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = o_0_0_xboole_0 )
      | ( sk_C = sk_B )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C = sk_A )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('30',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('32',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('33',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','30','31','32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ( X7 = X8 )
      | ( ( k2_tarski @ X7 @ X9 )
       != ( k2_tarski @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ sk_A @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = o_0_0_xboole_0 )
      | ( X1 = sk_D )
      | ( X1 = sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 = X10 )
      | ( ( k1_tarski @ X11 )
       != ( k2_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = o_0_0_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_D = sk_A )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 = X10 )
      | ( ( k1_tarski @ X11 )
       != ( k2_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_C )
        = o_0_0_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C = sk_A )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).


%------------------------------------------------------------------------------
