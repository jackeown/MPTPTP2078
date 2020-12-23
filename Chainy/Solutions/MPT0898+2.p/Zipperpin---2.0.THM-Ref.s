%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0898+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SdLhZ6GiV5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 13.82s
% Output     : Refutation 13.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  81 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 ( 796 expanded)
%              Number of equality atoms :   75 ( 153 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_78_type,type,(
    sk_B_78: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ ( A @ ( A @ ( A @ A ) ) ) )
        = ( k4_zfmisc_1 @ ( B @ ( B @ ( B @ B ) ) ) ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ ( A @ ( A @ ( A @ A ) ) ) )
          = ( k4_zfmisc_1 @ ( B @ ( B @ ( B @ B ) ) ) ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_B_78 @ ( sk_B_78 @ ( sk_B_78 @ sk_B_78 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k4_zfmisc_1 @ ( E @ ( F @ ( G @ H ) ) ) ) )
     => ( ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('1',plain,(
    ! [X4101: $i,X4102: $i,X4103: $i,X4104: $i,X4105: $i,X4106: $i,X4107: $i,X4108: $i] :
      ( ( ( k4_zfmisc_1 @ ( X4101 @ ( X4102 @ ( X4103 @ X4104 ) ) ) )
        = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4101 @ ( X4102 @ ( X4103 @ X4104 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4105 @ ( X4106 @ ( X4107 @ X4108 ) ) ) ) )
      | ( X4104 = X4108 ) ) ),
    inference(cnf,[status(esa)],[t57_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X4101: $i,X4102: $i,X4103: $i,X4104: $i,X4105: $i,X4106: $i,X4107: $i,X4108: $i] :
      ( ( ( k4_zfmisc_1 @ ( X4101 @ ( X4102 @ ( X4103 @ X4104 ) ) ) )
        = o_0_0_xboole_0 )
      | ( ( k4_zfmisc_1 @ ( X4101 @ ( X4102 @ ( X4103 @ X4104 ) ) ) )
       != ( k4_zfmisc_1 @ ( X4105 @ ( X4106 @ ( X4107 @ X4108 ) ) ) ) )
      | ( X4104 = X4108 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_B_78 = X0 )
      | ( ( k4_zfmisc_1 @ ( sk_B_78 @ ( sk_B_78 @ ( sk_B_78 @ sk_B_78 ) ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_B_78 @ ( sk_B_78 @ ( sk_B_78 @ sk_B_78 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
       != ( k4_zfmisc_1 @ ( X3 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      | ( sk_B_78 = X0 )
      | ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
      = o_0_0_xboole_0 )
    | ( sk_B_78 = sk_A_14 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    sk_A_14 != sk_B_78 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ ( A @ ( B @ ( C @ D ) ) ) )
       != k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4091: $i] :
      ( ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4091 ) ) ) )
       != k1_xboole_0 )
      | ( X4091 = k1_xboole_0 )
      | ( X4090 = k1_xboole_0 )
      | ( X4089 = k1_xboole_0 )
      | ( X4088 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

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
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4091: $i] :
      ( ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4091 ) ) ) )
       != o_0_0_xboole_0 )
      | ( X4091 = o_0_0_xboole_0 )
      | ( X4090 = o_0_0_xboole_0 )
      | ( X4089 = o_0_0_xboole_0 )
      | ( X4088 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('17',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    sk_A_14 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A_14 != sk_B_78 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
    = ( k4_zfmisc_1 @ ( sk_B_78 @ ( sk_B_78 @ ( sk_B_78 @ sk_B_78 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X4088: $i,X4089: $i,X4090: $i,X4091: $i] :
      ( ( ( k4_zfmisc_1 @ ( X4088 @ ( X4089 @ ( X4090 @ X4091 ) ) ) )
       != o_0_0_xboole_0 )
      | ( X4091 = o_0_0_xboole_0 )
      | ( X4090 = o_0_0_xboole_0 )
      | ( X4089 = o_0_0_xboole_0 )
      | ( X4088 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('22',plain,
    ( ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
     != o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 )
    | ( sk_B_78 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_78 = o_0_0_xboole_0 )
    | ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
     != o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( k4_zfmisc_1 @ ( sk_A_14 @ ( sk_A_14 @ ( sk_A_14 @ sk_A_14 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('25',plain,
    ( ( sk_B_78 = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B_78 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_A_14 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','27'])).

%------------------------------------------------------------------------------
