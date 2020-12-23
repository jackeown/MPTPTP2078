%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uQTmTtRnUN

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 (1478 expanded)
%              Number of leaves         :   24 ( 431 expanded)
%              Depth                    :   23
%              Number of atoms          : 1028 (18908 expanded)
%              Number of equality atoms :   36 ( 283 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t159_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t159_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k5_partfun1 @ X11 @ X12 @ X13 ) )
      | ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k5_partfun1 @ X11 @ X12 @ X13 ) )
      | ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k5_partfun1 @ X11 @ X12 @ X13 ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(t11_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_funct_2 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_partfun1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('50',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('53',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('56',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('59',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('68',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('69',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_funct_2 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_funct_2 @ k1_xboole_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X8 @ k1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['79','86'])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['56','90'])).


%------------------------------------------------------------------------------
