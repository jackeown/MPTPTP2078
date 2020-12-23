%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n5ucOpJPd1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:19 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  123 (1647 expanded)
%              Number of leaves         :   25 ( 480 expanded)
%              Depth                    :   23
%              Number of atoms          : 1086 (20268 expanded)
%              Number of equality atoms :   37 ( 313 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X21 @ X22 @ X23 ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X19 ) ) )
      | ( r2_hidden @ X18 @ ( k1_funct_2 @ X17 @ X19 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X15 @ X14 @ X16 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','49'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('64',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('65',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('73',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('74',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X19 ) ) )
      | ( r2_hidden @ X18 @ ( k1_funct_2 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_funct_2 @ k1_xboole_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ k1_xboole_0 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('87',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['61','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n5ucOpJPd1
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:33:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.88/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.14  % Solved by: fo/fo7.sh
% 0.88/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.14  % done 748 iterations in 0.678s
% 0.88/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.14  % SZS output start Refutation
% 0.88/1.14  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.88/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.88/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.88/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.14  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.88/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.88/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.88/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.88/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.88/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.88/1.14  thf(t159_funct_2, conjecture,
% 0.88/1.14    (![A:$i,B:$i,C:$i]:
% 0.88/1.14     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.14       ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.88/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.88/1.14        ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.14          ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )),
% 0.88/1.14    inference('cnf.neg', [status(esa)], [t159_funct_2])).
% 0.88/1.14  thf('0', plain,
% 0.88/1.14      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14          (k1_funct_2 @ sk_A @ sk_B))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf(d3_tarski, axiom,
% 0.88/1.14    (![A:$i,B:$i]:
% 0.88/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.88/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.88/1.14  thf('1', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf('2', plain,
% 0.88/1.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf(t158_funct_2, axiom,
% 0.88/1.14    (![A:$i,B:$i,C:$i]:
% 0.88/1.14     ( ( ( v1_funct_1 @ C ) & 
% 0.88/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.14       ( ![D:$i]:
% 0.88/1.14         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 0.88/1.14           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.88/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 0.88/1.14  thf('3', plain,
% 0.88/1.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.14         (~ (r2_hidden @ X20 @ (k5_partfun1 @ X21 @ X22 @ X23))
% 0.88/1.14          | (v1_funct_1 @ X20)
% 0.88/1.14          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.88/1.14          | ~ (v1_funct_1 @ X23))),
% 0.88/1.14      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.88/1.14  thf('4', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         (~ (v1_funct_1 @ sk_C_1)
% 0.88/1.14          | (v1_funct_1 @ X0)
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.88/1.14  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('6', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((v1_funct_1 @ X0)
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('demod', [status(thm)], ['4', '5'])).
% 0.88/1.14  thf('7', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.14      inference('sup-', [status(thm)], ['1', '6'])).
% 0.88/1.14  thf('8', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf('9', plain,
% 0.88/1.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('10', plain,
% 0.88/1.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.14         (~ (r2_hidden @ X20 @ (k5_partfun1 @ X21 @ X22 @ X23))
% 0.88/1.14          | (v1_funct_2 @ X20 @ X21 @ X22)
% 0.88/1.14          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.88/1.14          | ~ (v1_funct_1 @ X23))),
% 0.88/1.14      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.88/1.14  thf('11', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         (~ (v1_funct_1 @ sk_C_1)
% 0.88/1.14          | (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['9', '10'])).
% 0.88/1.14  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('13', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('demod', [status(thm)], ['11', '12'])).
% 0.88/1.14  thf('14', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             sk_A @ sk_B))),
% 0.88/1.14      inference('sup-', [status(thm)], ['8', '13'])).
% 0.88/1.14  thf('15', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf('16', plain,
% 0.88/1.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('17', plain,
% 0.88/1.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.14         (~ (r2_hidden @ X20 @ (k5_partfun1 @ X21 @ X22 @ X23))
% 0.88/1.14          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.88/1.14          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.88/1.14          | ~ (v1_funct_1 @ X23))),
% 0.88/1.14      inference('cnf', [status(esa)], [t158_funct_2])).
% 0.88/1.14  thf('18', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         (~ (v1_funct_1 @ sk_C_1)
% 0.88/1.14          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['16', '17'])).
% 0.88/1.14  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('20', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.88/1.14          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.88/1.14      inference('demod', [status(thm)], ['18', '19'])).
% 0.88/1.14  thf('21', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (m1_subset_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.88/1.14      inference('sup-', [status(thm)], ['15', '20'])).
% 0.88/1.14  thf(t11_funct_2, axiom,
% 0.88/1.14    (![A:$i,B:$i,C:$i]:
% 0.88/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.88/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.88/1.14         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.88/1.14  thf('22', plain,
% 0.88/1.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.88/1.14         (((X19) = (k1_xboole_0))
% 0.88/1.14          | ~ (v1_funct_1 @ X18)
% 0.88/1.14          | ~ (v1_funct_2 @ X18 @ X17 @ X19)
% 0.88/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X19)))
% 0.88/1.14          | (r2_hidden @ X18 @ (k1_funct_2 @ X17 @ X19)))),
% 0.88/1.14      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.88/1.14  thf('23', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ sk_A @ sk_B))
% 0.88/1.14          | ~ (v1_funct_2 @ 
% 0.88/1.14               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A @ sk_B)
% 0.88/1.14          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.14          | ((sk_B) = (k1_xboole_0)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.88/1.14  thf('24', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | ((sk_B) = (k1_xboole_0))
% 0.88/1.14          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.14          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ sk_A @ sk_B))
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['14', '23'])).
% 0.88/1.14  thf('25', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14           (k1_funct_2 @ sk_A @ sk_B))
% 0.88/1.14          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 0.88/1.14          | ((sk_B) = (k1_xboole_0))
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.14      inference('simplify', [status(thm)], ['24'])).
% 0.88/1.14  thf('26', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | ((sk_B) = (k1_xboole_0))
% 0.88/1.14          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['7', '25'])).
% 0.88/1.14  thf('27', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14           (k1_funct_2 @ sk_A @ sk_B))
% 0.88/1.14          | ((sk_B) = (k1_xboole_0))
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.88/1.14      inference('simplify', [status(thm)], ['26'])).
% 0.88/1.14  thf('28', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf('29', plain,
% 0.88/1.14      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14         (k1_funct_2 @ sk_A @ sk_B))
% 0.88/1.14        | ((sk_B) = (k1_xboole_0))
% 0.88/1.14        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14           (k1_funct_2 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['27', '28'])).
% 0.88/1.14  thf('30', plain,
% 0.88/1.14      ((((sk_B) = (k1_xboole_0))
% 0.88/1.14        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14           (k1_funct_2 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('simplify', [status(thm)], ['29'])).
% 0.88/1.14  thf('31', plain,
% 0.88/1.14      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14          (k1_funct_2 @ sk_A @ sk_B))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('34', plain,
% 0.88/1.14      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14          (k1_funct_2 @ sk_A @ k1_xboole_0))),
% 0.88/1.14      inference('demod', [status(thm)], ['0', '32', '33'])).
% 0.88/1.14  thf('35', plain,
% 0.88/1.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf(fc2_partfun1, axiom,
% 0.88/1.14    (![A:$i,B:$i,C:$i]:
% 0.88/1.14     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.88/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.88/1.14       ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ))).
% 0.88/1.14  thf('36', plain,
% 0.88/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.88/1.14         (~ (v1_xboole_0 @ X14)
% 0.88/1.14          | (v1_xboole_0 @ X15)
% 0.88/1.14          | ~ (v1_funct_1 @ X16)
% 0.88/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.88/1.14          | (v1_xboole_0 @ (k5_partfun1 @ X15 @ X14 @ X16)))),
% 0.88/1.14      inference('cnf', [status(esa)], [fc2_partfun1])).
% 0.88/1.14  thf('37', plain,
% 0.88/1.14      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.88/1.14        | ~ (v1_funct_1 @ sk_C_1)
% 0.88/1.14        | (v1_xboole_0 @ sk_A)
% 0.88/1.14        | ~ (v1_xboole_0 @ sk_B))),
% 0.88/1.14      inference('sup-', [status(thm)], ['35', '36'])).
% 0.88/1.14  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('39', plain,
% 0.88/1.14      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.88/1.14        | (v1_xboole_0 @ sk_A)
% 0.88/1.14        | ~ (v1_xboole_0 @ sk_B))),
% 0.88/1.14      inference('demod', [status(thm)], ['37', '38'])).
% 0.88/1.14  thf('40', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf(d10_xboole_0, axiom,
% 0.88/1.14    (![A:$i,B:$i]:
% 0.88/1.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.88/1.14  thf('41', plain,
% 0.88/1.14      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.88/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.14  thf('42', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.88/1.14      inference('simplify', [status(thm)], ['41'])).
% 0.88/1.14  thf(t3_subset, axiom,
% 0.88/1.14    (![A:$i,B:$i]:
% 0.88/1.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.88/1.14  thf('43', plain,
% 0.88/1.14      (![X8 : $i, X10 : $i]:
% 0.88/1.14         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.88/1.14      inference('cnf', [status(esa)], [t3_subset])).
% 0.88/1.14  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.14  thf(t5_subset, axiom,
% 0.88/1.14    (![A:$i,B:$i,C:$i]:
% 0.88/1.14     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.88/1.14          ( v1_xboole_0 @ C ) ) ))).
% 0.88/1.14  thf('45', plain,
% 0.88/1.14      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.88/1.14         (~ (r2_hidden @ X11 @ X12)
% 0.88/1.14          | ~ (v1_xboole_0 @ X13)
% 0.88/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.88/1.14      inference('cnf', [status(esa)], [t5_subset])).
% 0.88/1.14  thf('46', plain,
% 0.88/1.14      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.88/1.14  thf('47', plain,
% 0.88/1.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['40', '46'])).
% 0.88/1.14  thf('48', plain,
% 0.88/1.14      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.88/1.14          (k1_funct_2 @ sk_A @ sk_B))),
% 0.88/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.14  thf('49', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.88/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.88/1.14  thf('50', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.88/1.14      inference('clc', [status(thm)], ['39', '49'])).
% 0.88/1.14  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.88/1.14  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.88/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.88/1.14  thf('53', plain, ((v1_xboole_0 @ sk_A)),
% 0.88/1.14      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.88/1.14  thf('54', plain,
% 0.88/1.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['40', '46'])).
% 0.88/1.14  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.88/1.14  thf('55', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.88/1.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.88/1.14  thf('56', plain,
% 0.88/1.14      (![X4 : $i, X6 : $i]:
% 0.88/1.14         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.88/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.14  thf('57', plain,
% 0.88/1.14      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['55', '56'])).
% 0.88/1.14  thf('58', plain,
% 0.88/1.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['54', '57'])).
% 0.88/1.14  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('61', plain,
% 0.88/1.14      (~ (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 0.88/1.14      inference('demod', [status(thm)], ['34', '59', '60'])).
% 0.88/1.14  thf('62', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             sk_A @ sk_B))),
% 0.88/1.14      inference('sup-', [status(thm)], ['8', '13'])).
% 0.88/1.14  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('64', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('65', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('66', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_2 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             sk_A @ k1_xboole_0))),
% 0.88/1.14      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.88/1.14  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('70', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_2 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             k1_xboole_0 @ k1_xboole_0))),
% 0.88/1.14      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.88/1.14  thf('71', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (m1_subset_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.88/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.88/1.14      inference('sup-', [status(thm)], ['15', '20'])).
% 0.88/1.14  thf('72', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('73', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('74', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('75', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (m1_subset_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))),
% 0.88/1.14      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.88/1.14  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('79', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (m1_subset_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 0.88/1.14      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.88/1.14  thf('80', plain,
% 0.88/1.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.88/1.14         (((X17) != (k1_xboole_0))
% 0.88/1.14          | ~ (v1_funct_1 @ X18)
% 0.88/1.14          | ~ (v1_funct_2 @ X18 @ X17 @ X19)
% 0.88/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X19)))
% 0.88/1.14          | (r2_hidden @ X18 @ (k1_funct_2 @ X17 @ X19)))),
% 0.88/1.14      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.88/1.14  thf('81', plain,
% 0.88/1.14      (![X18 : $i, X19 : $i]:
% 0.88/1.14         ((r2_hidden @ X18 @ (k1_funct_2 @ k1_xboole_0 @ X19))
% 0.88/1.14          | ~ (m1_subset_1 @ X18 @ 
% 0.88/1.14               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X19)))
% 0.88/1.14          | ~ (v1_funct_2 @ X18 @ k1_xboole_0 @ X19)
% 0.88/1.14          | ~ (v1_funct_1 @ X18))),
% 0.88/1.14      inference('simplify', [status(thm)], ['80'])).
% 0.88/1.14  thf('82', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | ~ (v1_funct_1 @ 
% 0.88/1.14               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 0.88/1.14          | ~ (v1_funct_2 @ 
% 0.88/1.14               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14               k1_xboole_0 @ k1_xboole_0)
% 0.88/1.14          | (r2_hidden @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['79', '81'])).
% 0.88/1.14  thf('83', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (r2_hidden @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.88/1.14          | ~ (v1_funct_1 @ 
% 0.88/1.14               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14             X0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['70', '82'])).
% 0.88/1.14  thf('84', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         (~ (v1_funct_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 0.88/1.14          | (r2_hidden @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.88/1.14          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14             X0))),
% 0.88/1.14      inference('simplify', [status(thm)], ['83'])).
% 0.88/1.14  thf('85', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.88/1.14      inference('sup-', [status(thm)], ['1', '6'])).
% 0.88/1.14  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('87', plain, (((sk_B) = (k1_xboole_0))),
% 0.88/1.14      inference('clc', [status(thm)], ['30', '31'])).
% 0.88/1.14  thf('88', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1))))),
% 0.88/1.14      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.88/1.14  thf('89', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.88/1.14      inference('sup-', [status(thm)], ['53', '58'])).
% 0.88/1.14  thf('91', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (v1_funct_1 @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))))),
% 0.88/1.14      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.88/1.14  thf('92', plain,
% 0.88/1.14      (![X0 : $i]:
% 0.88/1.14         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 0.88/1.14          | (r2_hidden @ 
% 0.88/1.14             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 0.88/1.14             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.88/1.14      inference('clc', [status(thm)], ['84', '91'])).
% 0.88/1.14  thf('93', plain,
% 0.88/1.14      (![X1 : $i, X3 : $i]:
% 0.88/1.14         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.88/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.88/1.14  thf('94', plain,
% 0.88/1.14      (((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14         (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.88/1.14        | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14           (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.88/1.14      inference('sup-', [status(thm)], ['92', '93'])).
% 0.88/1.14  thf('95', plain,
% 0.88/1.14      ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 0.88/1.14        (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 0.88/1.14      inference('simplify', [status(thm)], ['94'])).
% 0.88/1.14  thf('96', plain, ($false), inference('demod', [status(thm)], ['61', '95'])).
% 0.88/1.14  
% 0.88/1.14  % SZS output end Refutation
% 0.88/1.14  
% 0.88/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
