%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nuH45jxvHo

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:19 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  129 (1280 expanded)
%              Number of leaves         :   26 ( 379 expanded)
%              Depth                    :   28
%              Number of atoms          : 1156 (15913 expanded)
%              Number of equality atoms :   32 ( 214 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X20 @ X21 @ X22 ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( r2_hidden @ X15 @ ( k1_funct_2 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_partfun1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('58',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','56','57'])).

thf('59',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k5_partfun1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k5_partfun1 @ X1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k5_partfun1 @ X1 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ X1 @ X0 @ sk_C_1 ) @ X2 )
      | ( v1_funct_2 @ ( sk_C @ X2 @ ( k5_partfun1 @ X1 @ X0 @ sk_C_1 ) ) @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('75',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('77',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf(t12_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_funct_2 @ X18 @ X18 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('91',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('92',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('99',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['58','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nuH45jxvHo
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.71/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.71/1.91  % Solved by: fo/fo7.sh
% 1.71/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.71/1.91  % done 1490 iterations in 1.451s
% 1.71/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.71/1.91  % SZS output start Refutation
% 1.71/1.91  thf(sk_B_type, type, sk_B: $i > $i).
% 1.71/1.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.71/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.71/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.71/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.71/1.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.71/1.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.71/1.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.71/1.91  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.71/1.91  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 1.71/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.71/1.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.71/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.71/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.71/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.71/1.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.71/1.91  thf(t159_funct_2, conjecture,
% 1.71/1.91    (![A:$i,B:$i,C:$i]:
% 1.71/1.91     ( ( ( v1_funct_1 @ C ) & 
% 1.71/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.71/1.91       ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ))).
% 1.71/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.71/1.91    (~( ![A:$i,B:$i,C:$i]:
% 1.71/1.91        ( ( ( v1_funct_1 @ C ) & 
% 1.71/1.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.71/1.91          ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )),
% 1.71/1.91    inference('cnf.neg', [status(esa)], [t159_funct_2])).
% 1.71/1.91  thf('0', plain,
% 1.71/1.91      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91          (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf(d3_tarski, axiom,
% 1.71/1.91    (![A:$i,B:$i]:
% 1.71/1.91     ( ( r1_tarski @ A @ B ) <=>
% 1.71/1.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.71/1.91  thf('1', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('2', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf(t158_funct_2, axiom,
% 1.71/1.91    (![A:$i,B:$i,C:$i]:
% 1.71/1.91     ( ( ( v1_funct_1 @ C ) & 
% 1.71/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.71/1.91       ( ![D:$i]:
% 1.71/1.91         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 1.71/1.91           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.71/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 1.71/1.91  thf('3', plain,
% 1.71/1.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.71/1.91         (~ (r2_hidden @ X19 @ (k5_partfun1 @ X20 @ X21 @ X22))
% 1.71/1.91          | (v1_funct_1 @ X19)
% 1.71/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.71/1.91          | ~ (v1_funct_1 @ X22))),
% 1.71/1.91      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.71/1.91  thf('4', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         (~ (v1_funct_1 @ sk_C_1)
% 1.71/1.91          | (v1_funct_1 @ X0)
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['2', '3'])).
% 1.71/1.91  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('6', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((v1_funct_1 @ X0)
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('demod', [status(thm)], ['4', '5'])).
% 1.71/1.91  thf('7', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 1.71/1.91      inference('sup-', [status(thm)], ['1', '6'])).
% 1.71/1.91  thf('8', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('9', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('10', plain,
% 1.71/1.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.71/1.91         (~ (r2_hidden @ X19 @ (k5_partfun1 @ X20 @ X21 @ X22))
% 1.71/1.91          | (v1_funct_2 @ X19 @ X20 @ X21)
% 1.71/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.71/1.91          | ~ (v1_funct_1 @ X22))),
% 1.71/1.91      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.71/1.91  thf('11', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         (~ (v1_funct_1 @ sk_C_1)
% 1.71/1.91          | (v1_funct_2 @ X0 @ sk_A @ sk_B_1)
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['9', '10'])).
% 1.71/1.91  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('13', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((v1_funct_2 @ X0 @ sk_A @ sk_B_1)
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('demod', [status(thm)], ['11', '12'])).
% 1.71/1.91  thf('14', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (v1_funct_2 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ sk_A @ 
% 1.71/1.91             sk_B_1))),
% 1.71/1.91      inference('sup-', [status(thm)], ['8', '13'])).
% 1.71/1.91  thf('15', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('16', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('17', plain,
% 1.71/1.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.71/1.91         (~ (r2_hidden @ X19 @ (k5_partfun1 @ X20 @ X21 @ X22))
% 1.71/1.91          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.71/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.71/1.91          | ~ (v1_funct_1 @ X22))),
% 1.71/1.91      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.71/1.91  thf('18', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         (~ (v1_funct_1 @ sk_C_1)
% 1.71/1.91          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['16', '17'])).
% 1.71/1.91  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('20', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.71/1.91          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.71/1.91      inference('demod', [status(thm)], ['18', '19'])).
% 1.71/1.91  thf('21', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (m1_subset_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.71/1.91      inference('sup-', [status(thm)], ['15', '20'])).
% 1.71/1.91  thf(t11_funct_2, axiom,
% 1.71/1.91    (![A:$i,B:$i,C:$i]:
% 1.71/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.71/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.71/1.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.71/1.91         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 1.71/1.91  thf('22', plain,
% 1.71/1.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.71/1.91         (((X16) = (k1_xboole_0))
% 1.71/1.91          | ~ (v1_funct_1 @ X15)
% 1.71/1.91          | ~ (v1_funct_2 @ X15 @ X14 @ X16)
% 1.71/1.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 1.71/1.91          | (r2_hidden @ X15 @ (k1_funct_2 @ X14 @ X16)))),
% 1.71/1.91      inference('cnf', [status(esa)], [t11_funct_2])).
% 1.71/1.91  thf('23', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ sk_A @ sk_B_1))
% 1.71/1.91          | ~ (v1_funct_2 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ sk_A @ 
% 1.71/1.91               sk_B_1)
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 1.71/1.91          | ((sk_B_1) = (k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['21', '22'])).
% 1.71/1.91  thf('24', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | ((sk_B_1) = (k1_xboole_0))
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ sk_A @ sk_B_1))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['14', '23'])).
% 1.71/1.91  thf('25', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91           (k1_funct_2 @ sk_A @ sk_B_1))
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 1.71/1.91          | ((sk_B_1) = (k1_xboole_0))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 1.71/1.91      inference('simplify', [status(thm)], ['24'])).
% 1.71/1.91  thf('26', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | ((sk_B_1) = (k1_xboole_0))
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['7', '25'])).
% 1.71/1.91  thf('27', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91           (k1_funct_2 @ sk_A @ sk_B_1))
% 1.71/1.91          | ((sk_B_1) = (k1_xboole_0))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 1.71/1.91      inference('simplify', [status(thm)], ['26'])).
% 1.71/1.91  thf('28', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('29', plain,
% 1.71/1.91      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91         (k1_funct_2 @ sk_A @ sk_B_1))
% 1.71/1.91        | ((sk_B_1) = (k1_xboole_0))
% 1.71/1.91        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91           (k1_funct_2 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['27', '28'])).
% 1.71/1.91  thf('30', plain,
% 1.71/1.91      ((((sk_B_1) = (k1_xboole_0))
% 1.71/1.91        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91           (k1_funct_2 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('simplify', [status(thm)], ['29'])).
% 1.71/1.91  thf('31', plain,
% 1.71/1.91      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91          (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('32', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('33', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('34', plain,
% 1.71/1.91      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91          (k1_funct_2 @ sk_A @ k1_xboole_0))),
% 1.71/1.91      inference('demod', [status(thm)], ['0', '32', '33'])).
% 1.71/1.91  thf('35', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf(fc2_partfun1, axiom,
% 1.71/1.91    (![A:$i,B:$i,C:$i]:
% 1.71/1.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.71/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.71/1.91       ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ))).
% 1.71/1.91  thf('36', plain,
% 1.71/1.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.71/1.91         (~ (v1_xboole_0 @ X11)
% 1.71/1.91          | (v1_xboole_0 @ X12)
% 1.71/1.91          | ~ (v1_funct_1 @ X13)
% 1.71/1.91          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 1.71/1.91          | (v1_xboole_0 @ (k5_partfun1 @ X12 @ X11 @ X13)))),
% 1.71/1.91      inference('cnf', [status(esa)], [fc2_partfun1])).
% 1.71/1.91  thf('37', plain,
% 1.71/1.91      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.71/1.91        | ~ (v1_funct_1 @ sk_C_1)
% 1.71/1.91        | (v1_xboole_0 @ sk_A)
% 1.71/1.91        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.71/1.91      inference('sup-', [status(thm)], ['35', '36'])).
% 1.71/1.91  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('39', plain,
% 1.71/1.91      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.71/1.91        | (v1_xboole_0 @ sk_A)
% 1.71/1.91        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.71/1.91      inference('demod', [status(thm)], ['37', '38'])).
% 1.71/1.91  thf('40', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf(d1_xboole_0, axiom,
% 1.71/1.91    (![A:$i]:
% 1.71/1.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.71/1.91  thf('41', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.71/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.71/1.91  thf('42', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['40', '41'])).
% 1.71/1.91  thf('43', plain,
% 1.71/1.91      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.71/1.91          (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('44', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.71/1.91      inference('sup-', [status(thm)], ['42', '43'])).
% 1.71/1.91  thf('45', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 1.71/1.91      inference('clc', [status(thm)], ['39', '44'])).
% 1.71/1.91  thf('46', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.71/1.91  thf('47', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.71/1.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.71/1.91  thf('48', plain,
% 1.71/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.71/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.71/1.91  thf(t7_ordinal1, axiom,
% 1.71/1.91    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.71/1.91  thf('49', plain,
% 1.71/1.91      (![X9 : $i, X10 : $i]:
% 1.71/1.91         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 1.71/1.91      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.71/1.91  thf('50', plain,
% 1.71/1.91      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['48', '49'])).
% 1.71/1.91  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.71/1.91      inference('sup-', [status(thm)], ['47', '50'])).
% 1.71/1.91  thf('52', plain, ((v1_xboole_0 @ sk_A)),
% 1.71/1.91      inference('demod', [status(thm)], ['45', '46', '51'])).
% 1.71/1.91  thf('53', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['40', '41'])).
% 1.71/1.91  thf(t3_xboole_1, axiom,
% 1.71/1.91    (![A:$i]:
% 1.71/1.91     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.71/1.91  thf('54', plain,
% 1.71/1.91      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 1.71/1.91      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.71/1.91  thf('55', plain,
% 1.71/1.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.71/1.91  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('58', plain,
% 1.71/1.91      (~ (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.71/1.91      inference('demod', [status(thm)], ['34', '56', '57'])).
% 1.71/1.91  thf('59', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('60', plain,
% 1.71/1.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.71/1.91  thf('61', plain,
% 1.71/1.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.71/1.91  thf('62', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('63', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('64', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ 
% 1.71/1.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 1.71/1.91      inference('demod', [status(thm)], ['62', '63'])).
% 1.71/1.91  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('66', plain,
% 1.71/1.91      ((m1_subset_1 @ sk_C_1 @ 
% 1.71/1.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.71/1.91      inference('demod', [status(thm)], ['64', '65'])).
% 1.71/1.91  thf('67', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((m1_subset_1 @ sk_C_1 @ 
% 1.71/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 1.71/1.91          | ~ (v1_xboole_0 @ X0))),
% 1.71/1.91      inference('sup+', [status(thm)], ['61', '66'])).
% 1.71/1.91  thf('68', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i]:
% 1.71/1.91         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.71/1.91          | ~ (v1_xboole_0 @ X0)
% 1.71/1.91          | ~ (v1_xboole_0 @ X1))),
% 1.71/1.91      inference('sup+', [status(thm)], ['60', '67'])).
% 1.71/1.91  thf('69', plain,
% 1.71/1.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.71/1.91         (~ (r2_hidden @ X19 @ (k5_partfun1 @ X20 @ X21 @ X22))
% 1.71/1.91          | (v1_funct_2 @ X19 @ X20 @ X21)
% 1.71/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.71/1.91          | ~ (v1_funct_1 @ X22))),
% 1.71/1.91      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.71/1.91  thf('70', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.91         (~ (v1_xboole_0 @ X1)
% 1.71/1.91          | ~ (v1_xboole_0 @ X0)
% 1.71/1.91          | ~ (v1_funct_1 @ sk_C_1)
% 1.71/1.91          | (v1_funct_2 @ X2 @ X1 @ X0)
% 1.71/1.91          | ~ (r2_hidden @ X2 @ (k5_partfun1 @ X1 @ X0 @ sk_C_1)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['68', '69'])).
% 1.71/1.91  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 1.71/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.91  thf('72', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.91         (~ (v1_xboole_0 @ X1)
% 1.71/1.91          | ~ (v1_xboole_0 @ X0)
% 1.71/1.91          | (v1_funct_2 @ X2 @ X1 @ X0)
% 1.71/1.91          | ~ (r2_hidden @ X2 @ (k5_partfun1 @ X1 @ X0 @ sk_C_1)))),
% 1.71/1.91      inference('demod', [status(thm)], ['70', '71'])).
% 1.71/1.91  thf('73', plain,
% 1.71/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ X1 @ X0 @ sk_C_1) @ X2)
% 1.71/1.91          | (v1_funct_2 @ (sk_C @ X2 @ (k5_partfun1 @ X1 @ X0 @ sk_C_1)) @ 
% 1.71/1.91             X1 @ X0)
% 1.71/1.91          | ~ (v1_xboole_0 @ X0)
% 1.71/1.91          | ~ (v1_xboole_0 @ X1))),
% 1.71/1.91      inference('sup-', [status(thm)], ['59', '72'])).
% 1.71/1.91  thf('74', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (m1_subset_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 1.71/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.71/1.91      inference('sup-', [status(thm)], ['15', '20'])).
% 1.71/1.91  thf('75', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('77', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('78', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (m1_subset_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))),
% 1.71/1.91      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.71/1.91  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('82', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (m1_subset_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.71/1.91      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 1.71/1.91  thf(t12_funct_2, axiom,
% 1.71/1.91    (![A:$i,B:$i]:
% 1.71/1.91     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.71/1.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.71/1.91       ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ))).
% 1.71/1.91  thf('83', plain,
% 1.71/1.91      (![X17 : $i, X18 : $i]:
% 1.71/1.91         ((r2_hidden @ X17 @ (k1_funct_2 @ X18 @ X18))
% 1.71/1.91          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.71/1.91          | ~ (v1_funct_2 @ X17 @ X18 @ X18)
% 1.71/1.91          | ~ (v1_funct_1 @ X17))),
% 1.71/1.91      inference('cnf', [status(esa)], [t12_funct_2])).
% 1.71/1.91  thf('84', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.71/1.91          | ~ (v1_funct_2 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91               k1_xboole_0 @ k1_xboole_0)
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['82', '83'])).
% 1.71/1.91  thf('85', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.71/1.91          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91             X0)
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91             X0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['73', '84'])).
% 1.71/1.91  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.71/1.91      inference('sup-', [status(thm)], ['47', '50'])).
% 1.71/1.91  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.71/1.91      inference('sup-', [status(thm)], ['47', '50'])).
% 1.71/1.91  thf('88', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 1.71/1.91          | ~ (v1_funct_1 @ 
% 1.71/1.91               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91             X0))),
% 1.71/1.91      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.71/1.91  thf('89', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         (~ (v1_funct_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 1.71/1.91          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91             X0))),
% 1.71/1.91      inference('simplify', [status(thm)], ['88'])).
% 1.71/1.91  thf('90', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.71/1.91          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 1.71/1.91      inference('sup-', [status(thm)], ['1', '6'])).
% 1.71/1.91  thf('91', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('92', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.71/1.91      inference('clc', [status(thm)], ['30', '31'])).
% 1.71/1.91  thf('93', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (v1_funct_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1))))),
% 1.71/1.91      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.71/1.91  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 1.71/1.91      inference('sup-', [status(thm)], ['52', '55'])).
% 1.71/1.91  thf('96', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (v1_funct_1 @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))))),
% 1.71/1.91      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.71/1.91  thf('97', plain,
% 1.71/1.91      (![X0 : $i]:
% 1.71/1.91         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.71/1.91          | (r2_hidden @ 
% 1.71/1.91             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 1.71/1.91             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.71/1.91      inference('clc', [status(thm)], ['89', '96'])).
% 1.71/1.91  thf('98', plain,
% 1.71/1.91      (![X4 : $i, X6 : $i]:
% 1.71/1.91         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.71/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.71/1.91  thf('99', plain,
% 1.71/1.91      (((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91         (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 1.71/1.91        | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91           (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.71/1.91      inference('sup-', [status(thm)], ['97', '98'])).
% 1.71/1.91  thf('100', plain,
% 1.71/1.91      ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 1.71/1.91        (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.71/1.91      inference('simplify', [status(thm)], ['99'])).
% 1.71/1.91  thf('101', plain, ($false), inference('demod', [status(thm)], ['58', '100'])).
% 1.71/1.91  
% 1.71/1.91  % SZS output end Refutation
% 1.71/1.91  
% 1.71/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
