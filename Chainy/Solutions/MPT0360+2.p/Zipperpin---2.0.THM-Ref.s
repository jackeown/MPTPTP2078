%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0360+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQLkFPAcUN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 5.93s
% Output     : Refutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  292 ( 445 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_20_type,type,(
    sk_C_20: $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( r1_tarski @ ( B @ C ) )
          & ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ C ) ) ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( ( r1_tarski @ ( B @ C ) )
            & ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ C ) ) ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,
    ( ( k6_subset_1 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( sk_B_8 @ sk_C_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( sk_B_8 @ sk_C_20 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,
    ( ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_xboole_0 @ ( B @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X368: $i,X369: $i,X370: $i] :
      ( ( r1_xboole_0 @ ( X368 @ ( k4_xboole_0 @ ( X369 @ X370 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X369 @ ( k4_xboole_0 @ ( X368 @ X370 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('18',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X368: $i,X369: $i,X370: $i] :
      ( ( r1_xboole_0 @ ( X368 @ ( k6_subset_1 @ ( X369 @ X370 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X369 @ ( k6_subset_1 @ ( X368 @ X370 ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) )
      | ( r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( X0 @ sk_C_20 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( X0 @ sk_C_20 ) ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('26',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k4_xboole_0 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k6_subset_1 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( sk_B_8 @ ( k6_subset_1 @ ( X0 @ sk_C_20 ) ) ) )
      = sk_B_8 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_B_8 = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['6','11','29'])).

thf('31',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    sk_B_8 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
