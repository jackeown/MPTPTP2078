%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0249+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uJrrKhL8wG

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:34 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  366 ( 701 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_tarski @ X11 )
       != ( k2_xboole_0 @ X9 @ X10 ) )
      | ( zip_tseitin_2 @ X10 @ X9 @ X11 )
      | ( zip_tseitin_1 @ X10 @ X9 @ X11 )
      | ( zip_tseitin_0 @ X10 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ sk_C )
       != ( k2_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(eq_res,[status(thm)],['2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X6 ) )
      | ~ ( zip_tseitin_2 @ X8 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(eq_res,[status(thm)],['2'])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ~ ( zip_tseitin_2 @ X8 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('18',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('22',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    zip_tseitin_0 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('29',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).


%------------------------------------------------------------------------------
