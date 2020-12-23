%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gPsteKPX9O

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:19 EST 2020

% Result     : Theorem 53.12s
% Output     : Refutation 53.12s
% Verified   : 
% Statistics : Number of formulae       :  129 (1720 expanded)
%              Number of leaves         :   24 ( 504 expanded)
%              Depth                    :   25
%              Number of atoms          : 1167 (20911 expanded)
%              Number of equality atoms :   37 ( 269 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k5_partfun1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k5_partfun1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k5_partfun1 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( r2_hidden @ X15 @ ( k1_funct_2 @ X14 @ X16 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X12 @ X11 @ X13 ) ) ) ),
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

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','51'])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('57',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('65',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( sk_C @ X1 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( sk_C @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('76',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('77',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('78',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( r2_hidden @ X15 @ ( k1_funct_2 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_funct_2 @ k1_xboole_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ k1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('93',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('94',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('97',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('101',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['61','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gPsteKPX9O
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 18:16:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 53.12/53.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 53.12/53.29  % Solved by: fo/fo7.sh
% 53.12/53.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 53.12/53.29  % done 5123 iterations in 52.824s
% 53.12/53.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 53.12/53.29  % SZS output start Refutation
% 53.12/53.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 53.12/53.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 53.12/53.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 53.12/53.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 53.12/53.29  thf(sk_A_type, type, sk_A: $i).
% 53.12/53.29  thf(sk_B_type, type, sk_B: $i).
% 53.12/53.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 53.12/53.29  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 53.12/53.29  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 53.12/53.29  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 53.12/53.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 53.12/53.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 53.12/53.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 53.12/53.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 53.12/53.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 53.12/53.29  thf(t159_funct_2, conjecture,
% 53.12/53.29    (![A:$i,B:$i,C:$i]:
% 53.12/53.29     ( ( ( v1_funct_1 @ C ) & 
% 53.12/53.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 53.12/53.29       ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ))).
% 53.12/53.29  thf(zf_stmt_0, negated_conjecture,
% 53.12/53.29    (~( ![A:$i,B:$i,C:$i]:
% 53.12/53.29        ( ( ( v1_funct_1 @ C ) & 
% 53.12/53.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 53.12/53.29          ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )),
% 53.12/53.29    inference('cnf.neg', [status(esa)], [t159_funct_2])).
% 53.12/53.29  thf('0', plain,
% 53.12/53.29      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29          (k1_funct_2 @ sk_A @ sk_B))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf(d3_tarski, axiom,
% 53.12/53.29    (![A:$i,B:$i]:
% 53.12/53.29     ( ( r1_tarski @ A @ B ) <=>
% 53.12/53.29       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 53.12/53.29  thf('1', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('2', plain,
% 53.12/53.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf(t158_funct_2, axiom,
% 53.12/53.29    (![A:$i,B:$i,C:$i]:
% 53.12/53.29     ( ( ( v1_funct_1 @ C ) & 
% 53.12/53.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 53.12/53.29       ( ![D:$i]:
% 53.12/53.29         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 53.12/53.29           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 53.12/53.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 53.12/53.29  thf('3', plain,
% 53.12/53.29      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 53.12/53.29         (~ (r2_hidden @ X17 @ (k5_partfun1 @ X18 @ X19 @ X20))
% 53.12/53.29          | (v1_funct_1 @ X17)
% 53.12/53.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 53.12/53.29          | ~ (v1_funct_1 @ X20))),
% 53.12/53.29      inference('cnf', [status(esa)], [t158_funct_2])).
% 53.12/53.29  thf('4', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         (~ (v1_funct_1 @ sk_C_1)
% 53.12/53.29          | (v1_funct_1 @ X0)
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['2', '3'])).
% 53.12/53.29  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('6', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((v1_funct_1 @ X0)
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('demod', [status(thm)], ['4', '5'])).
% 53.12/53.29  thf('7', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.12/53.29      inference('sup-', [status(thm)], ['1', '6'])).
% 53.12/53.29  thf('8', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('9', plain,
% 53.12/53.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('10', plain,
% 53.12/53.29      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 53.12/53.29         (~ (r2_hidden @ X17 @ (k5_partfun1 @ X18 @ X19 @ X20))
% 53.12/53.29          | (v1_funct_2 @ X17 @ X18 @ X19)
% 53.12/53.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 53.12/53.29          | ~ (v1_funct_1 @ X20))),
% 53.12/53.29      inference('cnf', [status(esa)], [t158_funct_2])).
% 53.12/53.29  thf('11', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         (~ (v1_funct_1 @ sk_C_1)
% 53.12/53.29          | (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['9', '10'])).
% 53.12/53.29  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('13', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((v1_funct_2 @ X0 @ sk_A @ sk_B)
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('demod', [status(thm)], ['11', '12'])).
% 53.12/53.29  thf('14', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             sk_A @ sk_B))),
% 53.12/53.29      inference('sup-', [status(thm)], ['8', '13'])).
% 53.12/53.29  thf('15', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('16', plain,
% 53.12/53.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('17', plain,
% 53.12/53.29      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 53.12/53.29         (~ (r2_hidden @ X17 @ (k5_partfun1 @ X18 @ X19 @ X20))
% 53.12/53.29          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 53.12/53.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 53.12/53.29          | ~ (v1_funct_1 @ X20))),
% 53.12/53.29      inference('cnf', [status(esa)], [t158_funct_2])).
% 53.12/53.29  thf('18', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         (~ (v1_funct_1 @ sk_C_1)
% 53.12/53.29          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['16', '17'])).
% 53.12/53.29  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('20', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 53.12/53.29          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.12/53.29      inference('demod', [status(thm)], ['18', '19'])).
% 53.12/53.29  thf('21', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (m1_subset_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 53.12/53.29      inference('sup-', [status(thm)], ['15', '20'])).
% 53.12/53.29  thf(t11_funct_2, axiom,
% 53.12/53.29    (![A:$i,B:$i,C:$i]:
% 53.12/53.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 53.12/53.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 53.12/53.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 53.12/53.29         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 53.12/53.29  thf('22', plain,
% 53.12/53.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 53.12/53.29         (((X16) = (k1_xboole_0))
% 53.12/53.29          | ~ (v1_funct_1 @ X15)
% 53.12/53.29          | ~ (v1_funct_2 @ X15 @ X14 @ X16)
% 53.12/53.29          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 53.12/53.29          | (r2_hidden @ X15 @ (k1_funct_2 @ X14 @ X16)))),
% 53.12/53.29      inference('cnf', [status(esa)], [t11_funct_2])).
% 53.12/53.29  thf('23', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ sk_A @ sk_B))
% 53.12/53.29          | ~ (v1_funct_2 @ 
% 53.12/53.29               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ sk_A @ sk_B)
% 53.12/53.29          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 53.12/53.29          | ((sk_B) = (k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['21', '22'])).
% 53.12/53.29  thf('24', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | ((sk_B) = (k1_xboole_0))
% 53.12/53.29          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 53.12/53.29          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ sk_A @ sk_B))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['14', '23'])).
% 53.12/53.29  thf('25', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29           (k1_funct_2 @ sk_A @ sk_B))
% 53.12/53.29          | ~ (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))
% 53.12/53.29          | ((sk_B) = (k1_xboole_0))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.12/53.29      inference('simplify', [status(thm)], ['24'])).
% 53.12/53.29  thf('26', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | ((sk_B) = (k1_xboole_0))
% 53.12/53.29          | (r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['7', '25'])).
% 53.12/53.29  thf('27', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29           (k1_funct_2 @ sk_A @ sk_B))
% 53.12/53.29          | ((sk_B) = (k1_xboole_0))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.12/53.29      inference('simplify', [status(thm)], ['26'])).
% 53.12/53.29  thf('28', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('29', plain,
% 53.12/53.29      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29         (k1_funct_2 @ sk_A @ sk_B))
% 53.12/53.29        | ((sk_B) = (k1_xboole_0))
% 53.12/53.29        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29           (k1_funct_2 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['27', '28'])).
% 53.12/53.29  thf('30', plain,
% 53.12/53.29      ((((sk_B) = (k1_xboole_0))
% 53.12/53.29        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29           (k1_funct_2 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('simplify', [status(thm)], ['29'])).
% 53.12/53.29  thf('31', plain,
% 53.12/53.29      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29          (k1_funct_2 @ sk_A @ sk_B))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('34', plain,
% 53.12/53.29      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29          (k1_funct_2 @ sk_A @ k1_xboole_0))),
% 53.12/53.29      inference('demod', [status(thm)], ['0', '32', '33'])).
% 53.12/53.29  thf('35', plain,
% 53.12/53.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf(fc2_partfun1, axiom,
% 53.12/53.29    (![A:$i,B:$i,C:$i]:
% 53.12/53.29     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) & ( v1_funct_1 @ C ) & 
% 53.12/53.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 53.12/53.29       ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ))).
% 53.12/53.29  thf('36', plain,
% 53.12/53.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 53.12/53.29         (~ (v1_xboole_0 @ X11)
% 53.12/53.29          | (v1_xboole_0 @ X12)
% 53.12/53.29          | ~ (v1_funct_1 @ X13)
% 53.12/53.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 53.12/53.29          | (v1_xboole_0 @ (k5_partfun1 @ X12 @ X11 @ X13)))),
% 53.12/53.29      inference('cnf', [status(esa)], [fc2_partfun1])).
% 53.12/53.29  thf('37', plain,
% 53.12/53.29      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 53.12/53.29        | ~ (v1_funct_1 @ sk_C_1)
% 53.12/53.29        | (v1_xboole_0 @ sk_A)
% 53.12/53.29        | ~ (v1_xboole_0 @ sk_B))),
% 53.12/53.29      inference('sup-', [status(thm)], ['35', '36'])).
% 53.12/53.29  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('39', plain,
% 53.12/53.29      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 53.12/53.29        | (v1_xboole_0 @ sk_A)
% 53.12/53.29        | ~ (v1_xboole_0 @ sk_B))),
% 53.12/53.29      inference('demod', [status(thm)], ['37', '38'])).
% 53.12/53.29  thf('40', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('41', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('42', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('43', plain,
% 53.12/53.29      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['41', '42'])).
% 53.12/53.29  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 53.12/53.29      inference('simplify', [status(thm)], ['43'])).
% 53.12/53.29  thf(t3_subset, axiom,
% 53.12/53.29    (![A:$i,B:$i]:
% 53.12/53.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 53.12/53.29  thf('45', plain,
% 53.12/53.29      (![X5 : $i, X7 : $i]:
% 53.12/53.29         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 53.12/53.29      inference('cnf', [status(esa)], [t3_subset])).
% 53.12/53.29  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['44', '45'])).
% 53.12/53.29  thf(t5_subset, axiom,
% 53.12/53.29    (![A:$i,B:$i,C:$i]:
% 53.12/53.29     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 53.12/53.29          ( v1_xboole_0 @ C ) ) ))).
% 53.12/53.29  thf('47', plain,
% 53.12/53.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.12/53.29         (~ (r2_hidden @ X8 @ X9)
% 53.12/53.29          | ~ (v1_xboole_0 @ X10)
% 53.12/53.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 53.12/53.29      inference('cnf', [status(esa)], [t5_subset])).
% 53.12/53.29  thf('48', plain,
% 53.12/53.29      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['46', '47'])).
% 53.12/53.29  thf('49', plain,
% 53.12/53.29      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['40', '48'])).
% 53.12/53.29  thf('50', plain,
% 53.12/53.29      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ 
% 53.12/53.29          (k1_funct_2 @ sk_A @ sk_B))),
% 53.12/53.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.12/53.29  thf('51', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 53.12/53.29      inference('sup-', [status(thm)], ['49', '50'])).
% 53.12/53.29  thf('52', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 53.12/53.29      inference('clc', [status(thm)], ['39', '51'])).
% 53.12/53.29  thf('53', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 53.12/53.29  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 53.12/53.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 53.12/53.29  thf('55', plain, ((v1_xboole_0 @ sk_A)),
% 53.12/53.29      inference('demod', [status(thm)], ['52', '53', '54'])).
% 53.12/53.29  thf('56', plain,
% 53.12/53.29      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['40', '48'])).
% 53.12/53.29  thf(t3_xboole_1, axiom,
% 53.12/53.29    (![A:$i]:
% 53.12/53.29     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 53.12/53.29  thf('57', plain,
% 53.12/53.29      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 53.12/53.29      inference('cnf', [status(esa)], [t3_xboole_1])).
% 53.12/53.29  thf('58', plain,
% 53.12/53.29      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['56', '57'])).
% 53.12/53.29  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('61', plain,
% 53.12/53.29      (~ (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 53.12/53.29      inference('demod', [status(thm)], ['34', '59', '60'])).
% 53.12/53.29  thf('62', plain,
% 53.12/53.29      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['56', '57'])).
% 53.12/53.29  thf('63', plain,
% 53.12/53.29      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['56', '57'])).
% 53.12/53.29  thf('64', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_2 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             sk_A @ sk_B))),
% 53.12/53.29      inference('sup-', [status(thm)], ['8', '13'])).
% 53.12/53.29  thf('65', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('68', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_2 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             sk_A @ k1_xboole_0))),
% 53.12/53.29      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 53.12/53.29  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('72', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_2 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             k1_xboole_0 @ k1_xboole_0))),
% 53.12/53.29      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 53.12/53.29  thf('73', plain,
% 53.12/53.29      (![X0 : $i, X1 : $i]:
% 53.12/53.29         ((v1_funct_2 @ 
% 53.12/53.29           (sk_C @ X1 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29           X0 @ k1_xboole_0)
% 53.12/53.29          | ~ (v1_xboole_0 @ X0)
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X1))),
% 53.12/53.29      inference('sup+', [status(thm)], ['63', '72'])).
% 53.12/53.29  thf('74', plain,
% 53.12/53.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.12/53.29         ((v1_funct_2 @ 
% 53.12/53.29           (sk_C @ X2 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29           X1 @ X0)
% 53.12/53.29          | ~ (v1_xboole_0 @ X0)
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X2)
% 53.12/53.29          | ~ (v1_xboole_0 @ X1))),
% 53.12/53.29      inference('sup+', [status(thm)], ['62', '73'])).
% 53.12/53.29  thf('75', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (m1_subset_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.12/53.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 53.12/53.29      inference('sup-', [status(thm)], ['15', '20'])).
% 53.12/53.29  thf('76', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('77', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('78', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('79', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (m1_subset_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))),
% 53.12/53.29      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 53.12/53.29  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('83', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (m1_subset_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 53.12/53.29      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 53.12/53.29  thf('84', plain,
% 53.12/53.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 53.12/53.29         (((X14) != (k1_xboole_0))
% 53.12/53.29          | ~ (v1_funct_1 @ X15)
% 53.12/53.29          | ~ (v1_funct_2 @ X15 @ X14 @ X16)
% 53.12/53.29          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 53.12/53.29          | (r2_hidden @ X15 @ (k1_funct_2 @ X14 @ X16)))),
% 53.12/53.29      inference('cnf', [status(esa)], [t11_funct_2])).
% 53.12/53.29  thf('85', plain,
% 53.12/53.29      (![X15 : $i, X16 : $i]:
% 53.12/53.29         ((r2_hidden @ X15 @ (k1_funct_2 @ k1_xboole_0 @ X16))
% 53.12/53.29          | ~ (m1_subset_1 @ X15 @ 
% 53.12/53.29               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X16)))
% 53.12/53.29          | ~ (v1_funct_2 @ X15 @ k1_xboole_0 @ X16)
% 53.12/53.29          | ~ (v1_funct_1 @ X15))),
% 53.12/53.29      inference('simplify', [status(thm)], ['84'])).
% 53.12/53.29  thf('86', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | ~ (v1_funct_1 @ 
% 53.12/53.29               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 53.12/53.29          | ~ (v1_funct_2 @ 
% 53.12/53.29               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29               k1_xboole_0 @ k1_xboole_0)
% 53.12/53.29          | (r2_hidden @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['83', '85'])).
% 53.12/53.29  thf('87', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         (~ (v1_xboole_0 @ k1_xboole_0)
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X0)
% 53.12/53.29          | ~ (v1_xboole_0 @ k1_xboole_0)
% 53.12/53.29          | (r2_hidden @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 53.12/53.29          | ~ (v1_funct_1 @ 
% 53.12/53.29               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['74', '86'])).
% 53.12/53.29  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 53.12/53.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 53.12/53.29  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 53.12/53.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 53.12/53.29  thf('90', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (r2_hidden @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 53.12/53.29          | ~ (v1_funct_1 @ 
% 53.12/53.29               (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X0))),
% 53.12/53.29      inference('demod', [status(thm)], ['87', '88', '89'])).
% 53.12/53.29  thf('91', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         (~ (v1_funct_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 53.12/53.29          | (r2_hidden @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 53.12/53.29          | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29             X0))),
% 53.12/53.29      inference('simplify', [status(thm)], ['90'])).
% 53.12/53.29  thf('92', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.12/53.29      inference('sup-', [status(thm)], ['1', '6'])).
% 53.12/53.29  thf('93', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('94', plain, (((sk_B) = (k1_xboole_0))),
% 53.12/53.29      inference('clc', [status(thm)], ['30', '31'])).
% 53.12/53.29  thf('95', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1))))),
% 53.12/53.29      inference('demod', [status(thm)], ['92', '93', '94'])).
% 53.12/53.29  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('97', plain, (((sk_A) = (k1_xboole_0))),
% 53.12/53.29      inference('sup-', [status(thm)], ['55', '58'])).
% 53.12/53.29  thf('98', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (v1_funct_1 @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))))),
% 53.12/53.29      inference('demod', [status(thm)], ['95', '96', '97'])).
% 53.12/53.29  thf('99', plain,
% 53.12/53.29      (![X0 : $i]:
% 53.12/53.29         ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ X0)
% 53.12/53.29          | (r2_hidden @ 
% 53.12/53.29             (sk_C @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1)) @ 
% 53.12/53.29             (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 53.12/53.29      inference('clc', [status(thm)], ['91', '98'])).
% 53.12/53.29  thf('100', plain,
% 53.12/53.29      (![X1 : $i, X3 : $i]:
% 53.12/53.29         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 53.12/53.29      inference('cnf', [status(esa)], [d3_tarski])).
% 53.12/53.29  thf('101', plain,
% 53.12/53.29      (((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29         (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 53.12/53.29        | (r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29           (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 53.12/53.29      inference('sup-', [status(thm)], ['99', '100'])).
% 53.12/53.29  thf('102', plain,
% 53.12/53.29      ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 53.12/53.29        (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 53.12/53.29      inference('simplify', [status(thm)], ['101'])).
% 53.12/53.29  thf('103', plain, ($false), inference('demod', [status(thm)], ['61', '102'])).
% 53.12/53.29  
% 53.12/53.29  % SZS output end Refutation
% 53.12/53.29  
% 53.12/53.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
