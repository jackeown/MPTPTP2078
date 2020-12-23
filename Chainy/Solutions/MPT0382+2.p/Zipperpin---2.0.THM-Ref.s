%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0382+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGbn4FO9Mx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 6.04s
% Output     : Refutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 143 expanded)
%              Number of leaves         :   30 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  503 ( 970 expanded)
%              Number of equality atoms :   56 ( 114 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_21_type,type,(
    sk_C_21: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t64_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( k3_subset_1 @ ( A @ B ) )
              = ( k3_subset_1 @ ( A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( ( k3_subset_1 @ ( A @ B ) )
                = ( k3_subset_1 @ ( A @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_subset_1])).

thf('0',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k3_subset_1 @ ( sk_A_2 @ sk_C_21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1542: $i,X1543: $i] :
      ( ( ( k3_subset_1 @ ( X1542 @ X1543 ) )
        = ( k4_xboole_0 @ ( X1542 @ X1543 ) ) )
      | ~ ( m1_subset_1 @ ( X1543 @ ( k1_zfmisc_1 @ X1542 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X1542: $i,X1543: $i] :
      ( ( ( k3_subset_1 @ ( X1542 @ X1543 ) )
        = ( k6_subset_1 @ ( X1542 @ X1543 ) ) )
      | ~ ( m1_subset_1 @ ( X1543 @ ( k1_zfmisc_1 @ X1542 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k3_subset_1 @ ( sk_A_2 @ sk_C_21 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ ( sk_C_21 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X1542: $i,X1543: $i] :
      ( ( ( k3_subset_1 @ ( X1542 @ X1543 ) )
        = ( k6_subset_1 @ ( X1542 @ X1543 ) ) )
      | ~ ( m1_subset_1 @ ( X1543 @ ( k1_zfmisc_1 @ X1542 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('9',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_21 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_21 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_21 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k4_xboole_0 @ ( X266 @ ( k4_xboole_0 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
    = ( k3_xboole_0 @ ( sk_A_2 @ sk_C_21 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X1589: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1589 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( A @ ( k3_tarski @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1058: $i,X1059: $i] :
      ( ( r1_tarski @ ( X1058 @ ( k3_tarski @ X1059 ) ) )
      | ~ ( r2_hidden @ ( X1058 @ X1059 ) ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( sk_B_8 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('26',plain,(
    ! [X1447: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X1447 ) )
      = X1447 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ ( sk_B_8 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('28',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( sk_B_8 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,
    ( ( k6_subset_1 @ ( sk_B_8 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('34',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ k1_xboole_0 ) )
      = X244 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X244: $i] :
      ( ( k6_subset_1 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('41',plain,(
    m1_subset_1 @ ( sk_C_21 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_C_21 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1589: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1589 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    r2_hidden @ ( sk_C_21 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1058: $i,X1059: $i] :
      ( ( r1_tarski @ ( X1058 @ ( k3_tarski @ X1059 ) ) )
      | ~ ( r2_hidden @ ( X1058 @ X1059 ) ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('47',plain,(
    r1_tarski @ ( sk_C_21 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1447: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X1447 ) )
      = X1447 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('49',plain,(
    r1_tarski @ ( sk_C_21 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('50',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ ( sk_C_21 @ sk_A_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X262: $i,X263: $i] :
      ( ( k4_xboole_0 @ ( X262 @ ( k2_xboole_0 @ ( X262 @ X263 ) ) ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('53',plain,(
    ! [X1644: $i,X1645: $i] :
      ( ( k6_subset_1 @ ( X1644 @ X1645 ) )
      = ( k4_xboole_0 @ ( X1644 @ X1645 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    ! [X262: $i,X263: $i] :
      ( ( k6_subset_1 @ ( X262 @ ( k2_xboole_0 @ ( X262 @ X263 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k6_subset_1 @ ( sk_C_21 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X244: $i] :
      ( ( k6_subset_1 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('58',plain,(
    sk_B_8 = sk_C_21 ),
    inference(demod,[status(thm)],['15','16','17','18','33','38','39','40','56','57'])).

thf('59',plain,(
    sk_B_8 != sk_C_21 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
