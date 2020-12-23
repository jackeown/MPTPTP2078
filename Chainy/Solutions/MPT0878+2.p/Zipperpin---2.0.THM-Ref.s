%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0878+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YEKw7VO9Om

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 9.93s
% Output     : Refutation 9.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  77 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  304 ( 670 expanded)
%              Number of equality atoms :   67 ( 139 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_76_type,type,(
    sk_B_76: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(t38_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ ( A @ ( A @ A ) ) )
        = ( k3_zfmisc_1 @ ( B @ ( B @ B ) ) ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_zfmisc_1 @ ( A @ ( A @ A ) ) )
          = ( k3_zfmisc_1 @ ( B @ ( B @ B ) ) ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t38_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
    = ( k3_zfmisc_1 @ ( sk_B_76 @ ( sk_B_76 @ sk_B_76 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
        = ( k3_zfmisc_1 @ ( D @ ( E @ F ) ) ) )
     => ( ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('1',plain,(
    ! [X3957: $i,X3958: $i,X3959: $i,X3960: $i,X3961: $i,X3962: $i] :
      ( ( ( k3_zfmisc_1 @ ( X3957 @ ( X3958 @ X3959 ) ) )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3957 @ ( X3958 @ X3959 ) ) )
       != ( k3_zfmisc_1 @ ( X3960 @ ( X3961 @ X3962 ) ) ) )
      | ( X3959 = X3962 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X3957: $i,X3958: $i,X3959: $i,X3960: $i,X3961: $i,X3962: $i] :
      ( ( ( k3_zfmisc_1 @ ( X3957 @ ( X3958 @ X3959 ) ) )
        = o_0_0_xboole_0 )
      | ( ( k3_zfmisc_1 @ ( X3957 @ ( X3958 @ X3959 ) ) )
       != ( k3_zfmisc_1 @ ( X3960 @ ( X3961 @ X3962 ) ) ) )
      | ( X3959 = X3962 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
       != ( k3_zfmisc_1 @ ( X2 @ ( X1 @ X0 ) ) ) )
      | ( sk_B_76 = X0 )
      | ( ( k3_zfmisc_1 @ ( sk_B_76 @ ( sk_B_76 @ sk_B_76 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
    = ( k3_zfmisc_1 @ ( sk_B_76 @ ( sk_B_76 @ sk_B_76 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
       != ( k3_zfmisc_1 @ ( X2 @ ( X1 @ X0 ) ) ) )
      | ( sk_B_76 = X0 )
      | ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
      = o_0_0_xboole_0 )
    | ( sk_B_76 = sk_A_14 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    sk_A_14 != sk_B_76 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ ( A @ ( B @ C ) ) )
       != k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X3947: $i,X3948: $i,X3949: $i] :
      ( ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3949 ) ) )
       != k1_xboole_0 )
      | ( X3949 = k1_xboole_0 )
      | ( X3948 = k1_xboole_0 )
      | ( X3947 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X3947: $i,X3948: $i,X3949: $i] :
      ( ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3949 ) ) )
       != o_0_0_xboole_0 )
      | ( X3949 = o_0_0_xboole_0 )
      | ( X3948 = o_0_0_xboole_0 )
      | ( X3947 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    sk_A_14 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_A_14 != sk_B_76 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
    = ( k3_zfmisc_1 @ ( sk_B_76 @ ( sk_B_76 @ sk_B_76 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X3947: $i,X3948: $i,X3949: $i] :
      ( ( ( k3_zfmisc_1 @ ( X3947 @ ( X3948 @ X3949 ) ) )
       != o_0_0_xboole_0 )
      | ( X3949 = o_0_0_xboole_0 )
      | ( X3948 = o_0_0_xboole_0 )
      | ( X3947 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('21',plain,
    ( ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
     != o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 )
    | ( sk_B_76 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_76 = o_0_0_xboole_0 )
    | ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
     != o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k3_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('24',plain,
    ( ( sk_B_76 = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B_76 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A_14 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','26'])).

%------------------------------------------------------------------------------
