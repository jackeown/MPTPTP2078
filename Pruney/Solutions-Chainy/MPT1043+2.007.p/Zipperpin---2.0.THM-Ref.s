%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QmvjMxAZwa

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:18 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  152 (3369 expanded)
%              Number of leaves         :   27 ( 974 expanded)
%              Depth                    :   22
%              Number of atoms          : 1198 (42930 expanded)
%              Number of equality atoms :   57 ( 783 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k5_partfun1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k5_partfun1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k5_partfun1 @ X32 @ X33 @ X34 ) )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( r2_hidden @ X27 @ ( k1_funct_2 @ X26 @ X28 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X24 @ X23 @ X25 ) ) ) ),
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
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('71',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('72',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('73',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('75',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','61','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('84',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('87',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('88',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( k1_xboole_0
        = ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86','87','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('91',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('92',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('93',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('96',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('97',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('101',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('103',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','60'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','61','73','74'])).

thf('109',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t12_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )).

thf('111',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ ( k1_funct_2 @ X30 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_2])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','69','70','71','72'])).

thf('115',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('119',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['75','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QmvjMxAZwa
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.76/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.76/1.92  % Solved by: fo/fo7.sh
% 1.76/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.92  % done 2515 iterations in 1.466s
% 1.76/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.76/1.92  % SZS output start Refutation
% 1.76/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.92  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.76/1.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.76/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.76/1.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.76/1.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.76/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.76/1.92  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 1.76/1.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.76/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.76/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.76/1.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.76/1.92  thf(t159_funct_2, conjecture,
% 1.76/1.92    (![A:$i,B:$i,C:$i]:
% 1.76/1.92     ( ( ( v1_funct_1 @ C ) & 
% 1.76/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.92       ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ))).
% 1.76/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.92    (~( ![A:$i,B:$i,C:$i]:
% 1.76/1.92        ( ( ( v1_funct_1 @ C ) & 
% 1.76/1.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.92          ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )),
% 1.76/1.92    inference('cnf.neg', [status(esa)], [t159_funct_2])).
% 1.76/1.92  thf('0', plain,
% 1.76/1.92      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92          (k1_funct_2 @ sk_A @ sk_B))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf(d3_tarski, axiom,
% 1.76/1.92    (![A:$i,B:$i]:
% 1.76/1.92     ( ( r1_tarski @ A @ B ) <=>
% 1.76/1.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.76/1.92  thf('1', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf('2', plain,
% 1.76/1.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf(t158_funct_2, axiom,
% 1.76/1.92    (![A:$i,B:$i,C:$i]:
% 1.76/1.92     ( ( ( v1_funct_1 @ C ) & 
% 1.76/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.92       ( ![D:$i]:
% 1.76/1.92         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 1.76/1.92           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.76/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 1.76/1.92  thf('3', plain,
% 1.76/1.92      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.92         (~ (r2_hidden @ X31 @ (k5_partfun1 @ X32 @ X33 @ X34))
% 1.76/1.92          | (v1_funct_1 @ X31)
% 1.76/1.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.76/1.92          | ~ (v1_funct_1 @ X34))),
% 1.76/1.92      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.76/1.92  thf('4', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (v1_funct_1 @ sk_C_1)
% 1.76/1.92          | (v1_funct_1 @ X0)
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['2', '3'])).
% 1.76/1.92  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('6', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((v1_funct_1 @ X0)
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('demod', [status(thm)], ['4', '5'])).
% 1.76/1.92  thf('7', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.76/1.92      inference('sup-', [status(thm)], ['1', '6'])).
% 1.76/1.92  thf('8', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf('9', plain,
% 1.76/1.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('10', plain,
% 1.76/1.92      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.92         (~ (r2_hidden @ X31 @ (k5_partfun1 @ X32 @ X33 @ X34))
% 1.76/1.92          | (v1_funct_2 @ X31 @ X32 @ X33)
% 1.76/1.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.76/1.92          | ~ (v1_funct_1 @ X34))),
% 1.76/1.92      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.76/1.92  thf('11', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (v1_funct_1 @ sk_C_1)
% 1.76/1.92          | (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['9', '10'])).
% 1.76/1.92  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('13', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('demod', [status(thm)], ['11', '12'])).
% 1.76/1.92  thf('14', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             sk_A @ sk_B))),
% 1.76/1.92      inference('sup-', [status(thm)], ['8', '13'])).
% 1.76/1.92  thf('15', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf('16', plain,
% 1.76/1.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('17', plain,
% 1.76/1.92      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.76/1.92         (~ (r2_hidden @ X31 @ (k5_partfun1 @ X32 @ X33 @ X34))
% 1.76/1.92          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.76/1.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.76/1.92          | ~ (v1_funct_1 @ X34))),
% 1.76/1.92      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.76/1.92  thf('18', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (v1_funct_1 @ sk_C_1)
% 1.76/1.92          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['16', '17'])).
% 1.76/1.92  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('20', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.76/1.92          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.76/1.92      inference('demod', [status(thm)], ['18', '19'])).
% 1.76/1.92  thf('21', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (m1_subset_1 @ 
% 1.76/1.92             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 1.76/1.92      inference('sup-', [status(thm)], ['15', '20'])).
% 1.76/1.92  thf(t11_funct_2, axiom,
% 1.76/1.92    (![A:$i,B:$i,C:$i]:
% 1.76/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.76/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.76/1.92         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 1.76/1.92  thf('22', plain,
% 1.76/1.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.76/1.92         (((X28) = (k1_xboole_0))
% 1.76/1.92          | ~ (v1_funct_1 @ X27)
% 1.76/1.92          | ~ (v1_funct_2 @ X27 @ X26 @ X28)
% 1.76/1.92          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 1.76/1.92          | (r2_hidden @ X27 @ (k1_funct_2 @ X26 @ X28)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t11_funct_2])).
% 1.76/1.92  thf('23', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k1_funct_2 @ sk_A @ sk_B))
% 1.76/1.92          | ~ (v1_funct_2 @ 
% 1.76/1.92               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A @ sk_B)
% 1.76/1.92          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 1.76/1.92          | ((sk_B) = (k1_xboole_0)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['21', '22'])).
% 1.76/1.92  thf('24', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | ((sk_B) = (k1_xboole_0))
% 1.76/1.92          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 1.76/1.92          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k1_funct_2 @ sk_A @ sk_B))
% 1.76/1.92          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['14', '23'])).
% 1.76/1.92  thf('25', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92           (k1_funct_2 @ sk_A @ sk_B))
% 1.76/1.92          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 1.76/1.92          | ((sk_B) = (k1_xboole_0))
% 1.76/1.92          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['24'])).
% 1.76/1.92  thf('26', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | ((sk_B) = (k1_xboole_0))
% 1.76/1.92          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k1_funct_2 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['7', '25'])).
% 1.76/1.92  thf('27', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92           (k1_funct_2 @ sk_A @ sk_B))
% 1.76/1.92          | ((sk_B) = (k1_xboole_0))
% 1.76/1.92          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['26'])).
% 1.76/1.92  thf('28', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf('29', plain,
% 1.76/1.92      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92         (k1_funct_2 @ sk_A @ sk_B))
% 1.76/1.92        | ((sk_B) = (k1_xboole_0))
% 1.76/1.92        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92           (k1_funct_2 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.76/1.92  thf('30', plain,
% 1.76/1.92      ((((sk_B) = (k1_xboole_0))
% 1.76/1.92        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92           (k1_funct_2 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('simplify', [status(thm)], ['29'])).
% 1.76/1.92  thf('31', plain,
% 1.76/1.92      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92          (k1_funct_2 @ sk_A @ sk_B))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('34', plain,
% 1.76/1.92      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ 
% 1.76/1.92          (k1_funct_2 @ sk_A @ k1_xboole_0))),
% 1.76/1.92      inference('demod', [status(thm)], ['0', '32', '33'])).
% 1.76/1.92  thf('35', plain,
% 1.76/1.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf(fc2_partfun1, axiom,
% 1.76/1.92    (![A:$i,B:$i,C:$i]:
% 1.76/1.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.76/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.76/1.92       ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ))).
% 1.76/1.92  thf('36', plain,
% 1.76/1.92      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.76/1.92         (~ (v1_xboole_0 @ X23)
% 1.76/1.92          | (v1_xboole_0 @ X24)
% 1.76/1.92          | ~ (v1_funct_1 @ X25)
% 1.76/1.92          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.76/1.92          | (v1_xboole_0 @ (k5_partfun1 @ X24 @ X23 @ X25)))),
% 1.76/1.92      inference('cnf', [status(esa)], [fc2_partfun1])).
% 1.76/1.92  thf('37', plain,
% 1.76/1.92      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 1.76/1.92        | ~ (v1_funct_1 @ sk_C_1)
% 1.76/1.92        | (v1_xboole_0 @ sk_A)
% 1.76/1.92        | ~ (v1_xboole_0 @ sk_B))),
% 1.76/1.92      inference('sup-', [status(thm)], ['35', '36'])).
% 1.76/1.92  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('39', plain,
% 1.76/1.92      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 1.76/1.92        | (v1_xboole_0 @ sk_A)
% 1.76/1.92        | ~ (v1_xboole_0 @ sk_B))),
% 1.76/1.92      inference('demod', [status(thm)], ['37', '38'])).
% 1.76/1.92  thf('40', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf(d10_xboole_0, axiom,
% 1.76/1.92    (![A:$i,B:$i]:
% 1.76/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.76/1.92  thf('41', plain,
% 1.76/1.92      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.76/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.76/1.92  thf('42', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.76/1.92      inference('simplify', [status(thm)], ['41'])).
% 1.76/1.92  thf(t3_subset, axiom,
% 1.76/1.92    (![A:$i,B:$i]:
% 1.76/1.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.76/1.92  thf('43', plain,
% 1.76/1.92      (![X11 : $i, X13 : $i]:
% 1.76/1.92         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.76/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.76/1.92  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['42', '43'])).
% 1.76/1.92  thf(t5_subset, axiom,
% 1.76/1.92    (![A:$i,B:$i,C:$i]:
% 1.76/1.92     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.76/1.92          ( v1_xboole_0 @ C ) ) ))).
% 1.76/1.92  thf('45', plain,
% 1.76/1.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.76/1.92         (~ (r2_hidden @ X17 @ X18)
% 1.76/1.92          | ~ (v1_xboole_0 @ X19)
% 1.76/1.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t5_subset])).
% 1.76/1.92  thf('46', plain,
% 1.76/1.92      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['44', '45'])).
% 1.76/1.92  thf('47', plain,
% 1.76/1.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['40', '46'])).
% 1.76/1.92  thf('48', plain,
% 1.76/1.92      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 1.76/1.92          (k1_funct_2 @ sk_A @ sk_B))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('49', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 1.76/1.92      inference('sup-', [status(thm)], ['47', '48'])).
% 1.76/1.92  thf('50', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 1.76/1.92      inference('clc', [status(thm)], ['39', '49'])).
% 1.76/1.92  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.76/1.92  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.76/1.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.76/1.92  thf('53', plain, ((v1_xboole_0 @ sk_A)),
% 1.76/1.92      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.76/1.92  thf('54', plain,
% 1.76/1.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['40', '46'])).
% 1.76/1.92  thf(t4_subset_1, axiom,
% 1.76/1.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.76/1.92  thf('55', plain,
% 1.76/1.92      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.76/1.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.76/1.92  thf('56', plain,
% 1.76/1.92      (![X11 : $i, X12 : $i]:
% 1.76/1.92         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.76/1.92  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.76/1.92      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/1.92  thf('58', plain,
% 1.76/1.92      (![X4 : $i, X6 : $i]:
% 1.76/1.92         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.76/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.76/1.92  thf('59', plain,
% 1.76/1.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['57', '58'])).
% 1.76/1.92  thf('60', plain,
% 1.76/1.92      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['54', '59'])).
% 1.76/1.92  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('62', plain,
% 1.76/1.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('63', plain,
% 1.76/1.92      (![X11 : $i, X12 : $i]:
% 1.76/1.92         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.76/1.92  thf('64', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.76/1.92      inference('sup-', [status(thm)], ['62', '63'])).
% 1.76/1.92  thf('65', plain,
% 1.76/1.92      (![X4 : $i, X6 : $i]:
% 1.76/1.92         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.76/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.76/1.92  thf('66', plain,
% 1.76/1.92      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 1.76/1.92        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['64', '65'])).
% 1.76/1.92  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf(t113_zfmisc_1, axiom,
% 1.76/1.92    (![A:$i,B:$i]:
% 1.76/1.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.76/1.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.76/1.92  thf('68', plain,
% 1.76/1.92      (![X8 : $i, X9 : $i]:
% 1.76/1.92         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.76/1.92  thf('69', plain,
% 1.76/1.92      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['68'])).
% 1.76/1.92  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.76/1.92      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/1.92  thf('71', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('72', plain,
% 1.76/1.92      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['68'])).
% 1.76/1.92  thf('73', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('75', plain,
% 1.76/1.92      (~ (r1_tarski @ 
% 1.76/1.92          (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 1.76/1.92          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('demod', [status(thm)], ['34', '61', '73', '74'])).
% 1.76/1.92  thf('76', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (m1_subset_1 @ 
% 1.76/1.92             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 1.76/1.92      inference('sup-', [status(thm)], ['15', '20'])).
% 1.76/1.92  thf('77', plain,
% 1.76/1.92      (![X11 : $i, X12 : $i]:
% 1.76/1.92         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.76/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.76/1.92  thf('78', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (r1_tarski @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['76', '77'])).
% 1.76/1.92  thf('79', plain,
% 1.76/1.92      (![X4 : $i, X6 : $i]:
% 1.76/1.92         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.76/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.76/1.92  thf('80', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.76/1.92               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 1.76/1.92          | ((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.76/1.92              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.76/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.76/1.92  thf('81', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('83', plain,
% 1.76/1.92      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['68'])).
% 1.76/1.92  thf('84', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('85', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.76/1.92      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/1.92  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('87', plain,
% 1.76/1.92      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['68'])).
% 1.76/1.92  thf('88', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('89', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.76/1.92          | ((k1_xboole_0)
% 1.76/1.92              = (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1))))),
% 1.76/1.92      inference('demod', [status(thm)],
% 1.76/1.92                ['80', '81', '82', '83', '84', '85', '86', '87', '88'])).
% 1.76/1.92  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('91', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('92', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('93', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('94', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ 
% 1.76/1.92           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | ((k1_xboole_0)
% 1.76/1.92              = (sk_C @ X0 @ 
% 1.76/1.92                 (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.76/1.92      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 1.76/1.92  thf('95', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 1.76/1.92          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.76/1.92             sk_A @ sk_B))),
% 1.76/1.92      inference('sup-', [status(thm)], ['8', '13'])).
% 1.76/1.92  thf('96', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('97', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('98', plain, (((sk_B) = (k1_xboole_0))),
% 1.76/1.92      inference('clc', [status(thm)], ['30', '31'])).
% 1.76/1.92  thf('99', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 1.76/1.92          | (v1_funct_2 @ 
% 1.76/1.92             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 1.76/1.92             sk_A @ k1_xboole_0))),
% 1.76/1.92      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 1.76/1.92  thf('100', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('101', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('103', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['53', '60'])).
% 1.76/1.92  thf('105', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ 
% 1.76/1.92           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | (v1_funct_2 @ 
% 1.76/1.92             (sk_C @ X0 @ 
% 1.76/1.92              (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)) @ 
% 1.76/1.92             k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('demod', [status(thm)],
% 1.76/1.92                ['99', '100', '101', '102', '103', '104'])).
% 1.76/1.92  thf('106', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.76/1.92          | (r1_tarski @ 
% 1.76/1.92             (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | (r1_tarski @ 
% 1.76/1.92             (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 1.76/1.92      inference('sup+', [status(thm)], ['94', '105'])).
% 1.76/1.92  thf('107', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ 
% 1.76/1.92           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['106'])).
% 1.76/1.92  thf('108', plain,
% 1.76/1.92      (~ (r1_tarski @ 
% 1.76/1.92          (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 1.76/1.92          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('demod', [status(thm)], ['34', '61', '73', '74'])).
% 1.76/1.92  thf('109', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.76/1.92      inference('sup-', [status(thm)], ['107', '108'])).
% 1.76/1.92  thf('110', plain,
% 1.76/1.92      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.76/1.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.76/1.92  thf(t12_funct_2, axiom,
% 1.76/1.92    (![A:$i,B:$i]:
% 1.76/1.92     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.76/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.76/1.92       ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ))).
% 1.76/1.92  thf('111', plain,
% 1.76/1.92      (![X29 : $i, X30 : $i]:
% 1.76/1.92         ((r2_hidden @ X29 @ (k1_funct_2 @ X30 @ X30))
% 1.76/1.92          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.76/1.92          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 1.76/1.92          | ~ (v1_funct_1 @ X29))),
% 1.76/1.92      inference('cnf', [status(esa)], [t12_funct_2])).
% 1.76/1.92  thf('112', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (v1_funct_1 @ k1_xboole_0)
% 1.76/1.92          | ~ (v1_funct_2 @ k1_xboole_0 @ X0 @ X0)
% 1.76/1.92          | (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ X0 @ X0)))),
% 1.76/1.92      inference('sup-', [status(thm)], ['110', '111'])).
% 1.76/1.92  thf('113', plain, ((v1_funct_1 @ sk_C_1)),
% 1.76/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.92  thf('114', plain, (((k1_xboole_0) = (sk_C_1))),
% 1.76/1.92      inference('demod', [status(thm)], ['66', '67', '69', '70', '71', '72'])).
% 1.76/1.92  thf('115', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.76/1.92      inference('demod', [status(thm)], ['113', '114'])).
% 1.76/1.92  thf('116', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (v1_funct_2 @ k1_xboole_0 @ X0 @ X0)
% 1.76/1.92          | (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ X0 @ X0)))),
% 1.76/1.92      inference('demod', [status(thm)], ['112', '115'])).
% 1.76/1.92  thf('117', plain,
% 1.76/1.92      ((r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['109', '116'])).
% 1.76/1.92  thf('118', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ 
% 1.76/1.92           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | ((k1_xboole_0)
% 1.76/1.92              = (sk_C @ X0 @ 
% 1.76/1.92                 (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 1.76/1.92      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 1.76/1.92  thf('119', plain,
% 1.76/1.92      (![X1 : $i, X3 : $i]:
% 1.76/1.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.76/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.76/1.92  thf('120', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         (~ (r2_hidden @ k1_xboole_0 @ X0)
% 1.76/1.92          | (r1_tarski @ 
% 1.76/1.92             (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | (r1_tarski @ 
% 1.76/1.92             (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['118', '119'])).
% 1.76/1.92  thf('121', plain,
% 1.76/1.92      (![X0 : $i]:
% 1.76/1.92         ((r1_tarski @ 
% 1.76/1.92           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 1.76/1.92          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 1.76/1.92      inference('simplify', [status(thm)], ['120'])).
% 1.76/1.92  thf('122', plain,
% 1.76/1.92      ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 1.76/1.92        (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 1.76/1.92      inference('sup-', [status(thm)], ['117', '121'])).
% 1.76/1.92  thf('123', plain, ($false), inference('demod', [status(thm)], ['75', '122'])).
% 1.76/1.92  
% 1.76/1.92  % SZS output end Refutation
% 1.76/1.92  
% 1.76/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
