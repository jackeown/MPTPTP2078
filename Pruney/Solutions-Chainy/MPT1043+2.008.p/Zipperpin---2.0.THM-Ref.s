%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exaorEchj3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:19 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  207 (1536 expanded)
%              Number of leaves         :   30 ( 458 expanded)
%              Depth                    :   27
%              Number of atoms          : 1754 (18659 expanded)
%              Number of equality atoms :   57 ( 353 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( r2_hidden @ X26 @ ( k1_funct_2 @ X25 @ X27 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X23 @ X22 @ X24 ) ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('68',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('69',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['62','63','65','66','67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('71',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','52','69','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('74',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_B @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('80',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('81',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('82',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('86',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['62','63','65','66','67','68'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('88',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['62','63','65','66','67','68'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( v1_xboole_0 @ ( sk_C @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('94',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('97',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('98',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k5_partfun1 @ X0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_partfun1 @ X0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ( ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('115',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_funct_2 @ X3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_partfun1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X2 @ X1 @ X0 ) )
      | ( v1_funct_2 @ ( sk_B @ ( k5_partfun1 @ X2 @ X1 @ X0 ) ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X0 @ k1_xboole_0 @ X1 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_partfun1 @ X2 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X2 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','121'])).

thf('123',plain,(
    ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) )
    | ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('126',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('129',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('138',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['127','138'])).

thf('140',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('142',plain,(
    v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('144',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf(t12_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )).

thf('146',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_funct_2 @ X29 @ X29 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_2])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_funct_2 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ( ( sk_B @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('151',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('153',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k5_partfun1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_funct_1 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( k5_partfun1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X2 @ X1 @ X0 ) )
      | ( v1_funct_1 @ ( sk_B @ ( k5_partfun1 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_partfun1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k5_partfun1 @ X2 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('164',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('166',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('167',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('169',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['148','167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','169'])).

thf('171',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_C @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) )
      | ( r1_tarski @ X0 @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','172'])).

thf('174',plain,(
    r1_tarski @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['71','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exaorEchj3
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.66/2.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.66/2.87  % Solved by: fo/fo7.sh
% 2.66/2.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.87  % done 2154 iterations in 2.421s
% 2.66/2.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.66/2.87  % SZS output start Refutation
% 2.66/2.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.66/2.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.66/2.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.66/2.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.66/2.87  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 2.66/2.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.66/2.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.66/2.87  thf(sk_B_type, type, sk_B: $i > $i).
% 2.66/2.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.66/2.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.66/2.87  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.66/2.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.66/2.87  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 2.66/2.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.66/2.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.66/2.87  thf(t159_funct_2, conjecture,
% 2.66/2.87    (![A:$i,B:$i,C:$i]:
% 2.66/2.87     ( ( ( v1_funct_1 @ C ) & 
% 2.66/2.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.66/2.87       ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ))).
% 2.66/2.87  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.87    (~( ![A:$i,B:$i,C:$i]:
% 2.66/2.87        ( ( ( v1_funct_1 @ C ) & 
% 2.66/2.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.66/2.87          ( r1_tarski @ ( k5_partfun1 @ A @ B @ C ) @ ( k1_funct_2 @ A @ B ) ) ) )),
% 2.66/2.87    inference('cnf.neg', [status(esa)], [t159_funct_2])).
% 2.66/2.87  thf('0', plain,
% 2.66/2.87      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87          (k1_funct_2 @ sk_A @ sk_B_1))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf(d3_tarski, axiom,
% 2.66/2.87    (![A:$i,B:$i]:
% 2.66/2.87     ( ( r1_tarski @ A @ B ) <=>
% 2.66/2.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.66/2.87  thf('1', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('2', plain,
% 2.66/2.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf(t158_funct_2, axiom,
% 2.66/2.87    (![A:$i,B:$i,C:$i]:
% 2.66/2.87     ( ( ( v1_funct_1 @ C ) & 
% 2.66/2.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.66/2.87       ( ![D:$i]:
% 2.66/2.87         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 2.66/2.87           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.66/2.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 2.66/2.87  thf('3', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (v1_funct_1 @ X30)
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('4', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         (~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87          | (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['2', '3'])).
% 2.66/2.87  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('6', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((v1_funct_1 @ X0)
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('demod', [status(thm)], ['4', '5'])).
% 2.66/2.87  thf('7', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (v1_funct_1 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 2.66/2.87      inference('sup-', [status(thm)], ['1', '6'])).
% 2.66/2.87  thf('8', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('9', plain,
% 2.66/2.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('10', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (v1_funct_2 @ X30 @ X31 @ X32)
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('11', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         (~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87          | (v1_funct_2 @ X0 @ sk_A @ sk_B_1)
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['9', '10'])).
% 2.66/2.87  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('13', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((v1_funct_2 @ X0 @ sk_A @ sk_B_1)
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('demod', [status(thm)], ['11', '12'])).
% 2.66/2.87  thf('14', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (v1_funct_2 @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ sk_A @ 
% 2.66/2.87             sk_B_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['8', '13'])).
% 2.66/2.87  thf('15', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('16', plain,
% 2.66/2.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('17', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('18', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         (~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['16', '17'])).
% 2.66/2.87  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('20', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.66/2.87          | ~ (r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.66/2.87      inference('demod', [status(thm)], ['18', '19'])).
% 2.66/2.87  thf('21', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (m1_subset_1 @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 2.66/2.87      inference('sup-', [status(thm)], ['15', '20'])).
% 2.66/2.87  thf(t11_funct_2, axiom,
% 2.66/2.87    (![A:$i,B:$i,C:$i]:
% 2.66/2.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.66/2.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.66/2.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.66/2.87         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 2.66/2.87  thf('22', plain,
% 2.66/2.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.66/2.87         (((X27) = (k1_xboole_0))
% 2.66/2.87          | ~ (v1_funct_1 @ X26)
% 2.66/2.87          | ~ (v1_funct_2 @ X26 @ X25 @ X27)
% 2.66/2.87          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 2.66/2.87          | (r2_hidden @ X26 @ (k1_funct_2 @ X25 @ X27)))),
% 2.66/2.87      inference('cnf', [status(esa)], [t11_funct_2])).
% 2.66/2.87  thf('23', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (r2_hidden @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87             (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87          | ~ (v1_funct_2 @ 
% 2.66/2.87               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ sk_A @ 
% 2.66/2.87               sk_B_1)
% 2.66/2.87          | ~ (v1_funct_1 @ 
% 2.66/2.87               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 2.66/2.87          | ((sk_B_1) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['21', '22'])).
% 2.66/2.87  thf('24', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | ((sk_B_1) = (k1_xboole_0))
% 2.66/2.87          | ~ (v1_funct_1 @ 
% 2.66/2.87               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 2.66/2.87          | (r2_hidden @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87             (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['14', '23'])).
% 2.66/2.87  thf('25', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87           (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87          | ~ (v1_funct_1 @ 
% 2.66/2.87               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 2.66/2.87          | ((sk_B_1) = (k1_xboole_0))
% 2.66/2.87          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['24'])).
% 2.66/2.87  thf('26', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | ((sk_B_1) = (k1_xboole_0))
% 2.66/2.87          | (r2_hidden @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87             (k1_funct_2 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['7', '25'])).
% 2.66/2.87  thf('27', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r2_hidden @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87           (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87          | ((sk_B_1) = (k1_xboole_0))
% 2.66/2.87          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['26'])).
% 2.66/2.87  thf('28', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('29', plain,
% 2.66/2.87      (((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87         (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87        | ((sk_B_1) = (k1_xboole_0))
% 2.66/2.87        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87           (k1_funct_2 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['27', '28'])).
% 2.66/2.87  thf('30', plain,
% 2.66/2.87      ((((sk_B_1) = (k1_xboole_0))
% 2.66/2.87        | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87           (k1_funct_2 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('simplify', [status(thm)], ['29'])).
% 2.66/2.87  thf('31', plain,
% 2.66/2.87      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87          (k1_funct_2 @ sk_A @ sk_B_1))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('32', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('33', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('34', plain,
% 2.66/2.87      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ 
% 2.66/2.87          (k1_funct_2 @ sk_A @ k1_xboole_0))),
% 2.66/2.87      inference('demod', [status(thm)], ['0', '32', '33'])).
% 2.66/2.87  thf('35', plain,
% 2.66/2.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf(fc2_partfun1, axiom,
% 2.66/2.87    (![A:$i,B:$i,C:$i]:
% 2.66/2.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) & ( v1_funct_1 @ C ) & 
% 2.66/2.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.66/2.87       ( v1_xboole_0 @ ( k5_partfun1 @ A @ B @ C ) ) ))).
% 2.66/2.87  thf('36', plain,
% 2.66/2.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X22)
% 2.66/2.87          | (v1_xboole_0 @ X23)
% 2.66/2.87          | ~ (v1_funct_1 @ X24)
% 2.66/2.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X23 @ X22 @ X24)))),
% 2.66/2.87      inference('cnf', [status(esa)], [fc2_partfun1])).
% 2.66/2.87  thf('37', plain,
% 2.66/2.87      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))
% 2.66/2.87        | ~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87        | (v1_xboole_0 @ sk_A)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['35', '36'])).
% 2.66/2.87  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('39', plain,
% 2.66/2.87      (((v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))
% 2.66/2.87        | (v1_xboole_0 @ sk_A)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['37', '38'])).
% 2.66/2.87  thf('40', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf(d1_xboole_0, axiom,
% 2.66/2.87    (![A:$i]:
% 2.66/2.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.66/2.87  thf('41', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('42', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['40', '41'])).
% 2.66/2.87  thf('43', plain,
% 2.66/2.87      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87          (k1_funct_2 @ sk_A @ sk_B_1))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('44', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['42', '43'])).
% 2.66/2.87  thf('45', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 2.66/2.87      inference('clc', [status(thm)], ['39', '44'])).
% 2.66/2.87  thf('46', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.66/2.87  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('48', plain, ((v1_xboole_0 @ sk_A)),
% 2.66/2.87      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.66/2.87  thf('49', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['40', '41'])).
% 2.66/2.87  thf(t3_xboole_1, axiom,
% 2.66/2.87    (![A:$i]:
% 2.66/2.87     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.66/2.87  thf('50', plain,
% 2.66/2.87      (![X11 : $i]:
% 2.66/2.87         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 2.66/2.87      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.66/2.87  thf('51', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['48', '51'])).
% 2.66/2.87  thf('53', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('54', plain,
% 2.66/2.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf(l3_subset_1, axiom,
% 2.66/2.87    (![A:$i,B:$i]:
% 2.66/2.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.66/2.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.66/2.87  thf('55', plain,
% 2.66/2.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X15 @ X16)
% 2.66/2.87          | (r2_hidden @ X15 @ X17)
% 2.66/2.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.66/2.87      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.66/2.87  thf('56', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.66/2.87          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['54', '55'])).
% 2.66/2.87  thf('57', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ sk_C_1 @ X0)
% 2.66/2.87          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['53', '56'])).
% 2.66/2.87  thf('58', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('59', plain,
% 2.66/2.87      (((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.66/2.87        | (r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['57', '58'])).
% 2.66/2.87  thf('60', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 2.66/2.87      inference('simplify', [status(thm)], ['59'])).
% 2.66/2.87  thf(d10_xboole_0, axiom,
% 2.66/2.87    (![A:$i,B:$i]:
% 2.66/2.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.66/2.87  thf('61', plain,
% 2.66/2.87      (![X7 : $i, X9 : $i]:
% 2.66/2.87         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.66/2.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.66/2.87  thf('62', plain,
% 2.66/2.87      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 2.66/2.87        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['60', '61'])).
% 2.66/2.87  thf('63', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf(t113_zfmisc_1, axiom,
% 2.66/2.87    (![A:$i,B:$i]:
% 2.66/2.87     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.66/2.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.66/2.87  thf('64', plain,
% 2.66/2.87      (![X13 : $i, X14 : $i]:
% 2.66/2.87         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 2.66/2.87          | ((X14) != (k1_xboole_0)))),
% 2.66/2.87      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.66/2.87  thf('65', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.66/2.87  thf('66', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 2.66/2.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.66/2.87  thf('67', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('68', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf('69', plain, (((k1_xboole_0) = (sk_C_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['62', '63', '65', '66', '67', '68'])).
% 2.66/2.87  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['48', '51'])).
% 2.66/2.87  thf('71', plain,
% 2.66/2.87      (~ (r1_tarski @ 
% 2.66/2.87          (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 2.66/2.87          (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 2.66/2.87      inference('demod', [status(thm)], ['34', '52', '69', '70'])).
% 2.66/2.87  thf('72', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('73', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (m1_subset_1 @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 2.66/2.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 2.66/2.87      inference('sup-', [status(thm)], ['15', '20'])).
% 2.66/2.87  thf('74', plain,
% 2.66/2.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X15 @ X16)
% 2.66/2.87          | (r2_hidden @ X15 @ X17)
% 2.66/2.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.66/2.87      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.66/2.87  thf('75', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (r2_hidden @ X1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.66/2.87          | ~ (r2_hidden @ X1 @ 
% 2.66/2.87               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 2.66/2.87      inference('sup-', [status(thm)], ['73', '74'])).
% 2.66/2.87  thf('76', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 2.66/2.87          | (r2_hidden @ 
% 2.66/2.87             (sk_B @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))) @ 
% 2.66/2.87             (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.66/2.87          | (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['72', '75'])).
% 2.66/2.87  thf('77', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('78', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (sk_C @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 2.66/2.87          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['76', '77'])).
% 2.66/2.87  thf('79', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('80', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('81', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('82', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('84', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1) @ X0)
% 2.66/2.87          | (v1_xboole_0 @ 
% 2.66/2.87             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C_1))))),
% 2.66/2.87      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 2.66/2.87  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['48', '51'])).
% 2.66/2.87  thf('86', plain, (((k1_xboole_0) = (sk_C_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['62', '63', '65', '66', '67', '68'])).
% 2.66/2.87  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['48', '51'])).
% 2.66/2.87  thf('88', plain, (((k1_xboole_0) = (sk_C_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['62', '63', '65', '66', '67', '68'])).
% 2.66/2.87  thf('89', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r1_tarski @ 
% 2.66/2.87           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 2.66/2.87          | (v1_xboole_0 @ 
% 2.66/2.87             (sk_C @ X0 @ 
% 2.66/2.87              (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 2.66/2.87      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 2.66/2.87  thf('90', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('91', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('92', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('93', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf(t4_subset_1, axiom,
% 2.66/2.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.66/2.87  thf('94', plain,
% 2.66/2.87      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 2.66/2.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.66/2.87  thf('95', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['93', '94'])).
% 2.66/2.87  thf('96', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('97', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf('98', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('99', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | (m1_subset_1 @ X2 @ 
% 2.66/2.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 2.66/2.87          | ~ (r2_hidden @ X2 @ (k5_partfun1 @ X0 @ k1_xboole_0 @ X1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['97', '98'])).
% 2.66/2.87  thf('100', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf('101', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.66/2.87          | ~ (r2_hidden @ X2 @ (k5_partfun1 @ X0 @ k1_xboole_0 @ X1)))),
% 2.66/2.87      inference('demod', [status(thm)], ['99', '100'])).
% 2.66/2.87  thf('102', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | (m1_subset_1 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)) @ 
% 2.66/2.87             (k1_zfmisc_1 @ k1_xboole_0))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['96', '101'])).
% 2.66/2.87  thf('103', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (m1_subset_1 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)) @ 
% 2.66/2.87             (k1_zfmisc_1 @ k1_xboole_0))
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['95', '102'])).
% 2.66/2.87  thf('104', plain,
% 2.66/2.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X15 @ X16)
% 2.66/2.87          | (r2_hidden @ X15 @ X17)
% 2.66/2.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.66/2.87      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.66/2.87  thf('105', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | (r2_hidden @ X2 @ k1_xboole_0)
% 2.66/2.87          | ~ (r2_hidden @ X2 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))))),
% 2.66/2.87      inference('sup-', [status(thm)], ['103', '104'])).
% 2.66/2.87  thf('106', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)))
% 2.66/2.87          | (r2_hidden @ 
% 2.66/2.87             (sk_B @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))) @ 
% 2.66/2.87             k1_xboole_0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['92', '105'])).
% 2.66/2.87  thf('107', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('108', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)))
% 2.66/2.87          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['106', '107'])).
% 2.66/2.87  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('110', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))))),
% 2.66/2.87      inference('demod', [status(thm)], ['108', '109'])).
% 2.66/2.87  thf('111', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('112', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ((sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['110', '111'])).
% 2.66/2.87  thf('113', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('114', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['93', '94'])).
% 2.66/2.87  thf('115', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (v1_funct_2 @ X30 @ X31 @ X32)
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('116', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X2)
% 2.66/2.87          | ~ (v1_funct_1 @ X2)
% 2.66/2.87          | (v1_funct_2 @ X3 @ X1 @ X0)
% 2.66/2.87          | ~ (r2_hidden @ X3 @ (k5_partfun1 @ X1 @ X0 @ X2)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['114', '115'])).
% 2.66/2.87  thf('117', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X2 @ X1 @ X0))
% 2.66/2.87          | (v1_funct_2 @ (sk_B @ (k5_partfun1 @ X2 @ X1 @ X0)) @ X2 @ X1)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['113', '116'])).
% 2.66/2.87  thf('118', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X0 @ k1_xboole_0 @ X1))
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | ~ (v1_xboole_0 @ X1)
% 2.66/2.87          | ~ (v1_xboole_0 @ X1)
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X0 @ k1_xboole_0 @ X1)))),
% 2.66/2.87      inference('sup+', [status(thm)], ['112', '117'])).
% 2.66/2.87  thf('119', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X1)
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X0 @ k1_xboole_0 @ X1))
% 2.66/2.87          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['118'])).
% 2.66/2.87  thf('120', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('121', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_funct_2 @ k1_xboole_0 @ X1 @ k1_xboole_0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ((k5_partfun1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['119', '120'])).
% 2.66/2.87  thf('122', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         (((k5_partfun1 @ X2 @ X0 @ X1) = (k1_xboole_0))
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X1)
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | (v1_funct_2 @ k1_xboole_0 @ X2 @ k1_xboole_0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['91', '121'])).
% 2.66/2.87  thf('123', plain,
% 2.66/2.87      (~ (r1_tarski @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 2.66/2.87          (k1_funct_2 @ sk_A @ sk_B_1))),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('124', plain,
% 2.66/2.87      ((~ (r1_tarski @ k1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))
% 2.66/2.87        | (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['122', '123'])).
% 2.66/2.87  thf('125', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 2.66/2.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.66/2.87  thf('126', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('127', plain,
% 2.66/2.87      (((v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.66/2.87  thf('128', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('129', plain,
% 2.66/2.87      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.87  thf('130', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['128', '129'])).
% 2.66/2.87  thf('131', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('132', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.66/2.87          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['54', '55'])).
% 2.66/2.87  thf('133', plain,
% 2.66/2.87      (((v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | (r2_hidden @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['131', '132'])).
% 2.66/2.87  thf('134', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('135', plain,
% 2.66/2.87      (((v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['133', '134'])).
% 2.66/2.87  thf('136', plain,
% 2.66/2.87      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1)
% 2.66/2.87        | (v1_xboole_0 @ sk_C_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['130', '135'])).
% 2.66/2.87  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('138', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['136', '137'])).
% 2.66/2.87  thf('139', plain,
% 2.66/2.87      ((~ (v1_xboole_0 @ sk_B_1)
% 2.66/2.87        | (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['127', '138'])).
% 2.66/2.87  thf('140', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('142', plain, ((v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 2.66/2.87      inference('demod', [status(thm)], ['139', '140', '141'])).
% 2.66/2.87  thf('143', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['48', '51'])).
% 2.66/2.87  thf('144', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('demod', [status(thm)], ['142', '143'])).
% 2.66/2.87  thf('145', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['93', '94'])).
% 2.66/2.87  thf(t12_funct_2, axiom,
% 2.66/2.87    (![A:$i,B:$i]:
% 2.66/2.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.66/2.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.66/2.87       ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ))).
% 2.66/2.87  thf('146', plain,
% 2.66/2.87      (![X28 : $i, X29 : $i]:
% 2.66/2.87         ((r2_hidden @ X28 @ (k1_funct_2 @ X29 @ X29))
% 2.66/2.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 2.66/2.87          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 2.66/2.87          | ~ (v1_funct_1 @ X28))),
% 2.66/2.87      inference('cnf', [status(esa)], [t12_funct_2])).
% 2.66/2.87  thf('147', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X1)
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | ~ (v1_funct_2 @ X1 @ X0 @ X0)
% 2.66/2.87          | (r2_hidden @ X1 @ (k1_funct_2 @ X0 @ X0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['145', '146'])).
% 2.66/2.87  thf('148', plain,
% 2.66/2.87      (((r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 2.66/2.87        | ~ (v1_funct_1 @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['144', '147'])).
% 2.66/2.87  thf('149', plain,
% 2.66/2.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.87  thf('150', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ((sk_B @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['110', '111'])).
% 2.66/2.87  thf('151', plain,
% 2.66/2.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.66/2.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.87  thf('152', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['93', '94'])).
% 2.66/2.87  thf('153', plain,
% 2.66/2.87      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.66/2.87         (~ (r2_hidden @ X30 @ (k5_partfun1 @ X31 @ X32 @ X33))
% 2.66/2.87          | (v1_funct_1 @ X30)
% 2.66/2.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.66/2.87          | ~ (v1_funct_1 @ X33))),
% 2.66/2.87      inference('cnf', [status(esa)], [t158_funct_2])).
% 2.66/2.87  thf('154', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X2)
% 2.66/2.87          | ~ (v1_funct_1 @ X2)
% 2.66/2.87          | (v1_funct_1 @ X3)
% 2.66/2.87          | ~ (r2_hidden @ X3 @ (k5_partfun1 @ X1 @ X0 @ X2)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['152', '153'])).
% 2.66/2.87  thf('155', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X2 @ X1 @ X0))
% 2.66/2.87          | (v1_funct_1 @ (sk_B @ (k5_partfun1 @ X2 @ X1 @ X0)))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup-', [status(thm)], ['151', '154'])).
% 2.66/2.87  thf('156', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         ((v1_funct_1 @ k1_xboole_0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0)))),
% 2.66/2.87      inference('sup+', [status(thm)], ['150', '155'])).
% 2.66/2.87  thf('157', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ X0)
% 2.66/2.87          | ~ (v1_funct_1 @ X0)
% 2.66/2.87          | (v1_xboole_0 @ (k5_partfun1 @ X1 @ k1_xboole_0 @ X0))
% 2.66/2.87          | (v1_funct_1 @ k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['156'])).
% 2.66/2.87  thf('158', plain,
% 2.66/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.87         ((v1_xboole_0 @ (k5_partfun1 @ X2 @ X0 @ X1))
% 2.66/2.87          | ~ (v1_xboole_0 @ X0)
% 2.66/2.87          | (v1_funct_1 @ k1_xboole_0)
% 2.66/2.87          | ~ (v1_funct_1 @ X1)
% 2.66/2.87          | ~ (v1_xboole_0 @ X1))),
% 2.66/2.87      inference('sup+', [status(thm)], ['149', '157'])).
% 2.66/2.87  thf('159', plain, (~ (v1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['42', '43'])).
% 2.66/2.87  thf('160', plain,
% 2.66/2.87      ((~ (v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | ~ (v1_funct_1 @ sk_C_1)
% 2.66/2.87        | (v1_funct_1 @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('sup-', [status(thm)], ['158', '159'])).
% 2.66/2.87  thf('161', plain, ((v1_funct_1 @ sk_C_1)),
% 2.66/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.87  thf('162', plain,
% 2.66/2.87      ((~ (v1_xboole_0 @ sk_C_1)
% 2.66/2.87        | (v1_funct_1 @ k1_xboole_0)
% 2.66/2.87        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['160', '161'])).
% 2.66/2.87  thf('163', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 2.66/2.87      inference('demod', [status(thm)], ['136', '137'])).
% 2.66/2.87  thf('164', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_funct_1 @ k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['162', '163'])).
% 2.66/2.87  thf('165', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.66/2.87      inference('clc', [status(thm)], ['30', '31'])).
% 2.66/2.87  thf('166', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('167', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.66/2.87      inference('demod', [status(thm)], ['164', '165', '166'])).
% 2.66/2.87  thf('168', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.66/2.87  thf('169', plain,
% 2.66/2.87      ((r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 2.66/2.87      inference('demod', [status(thm)], ['148', '167', '168'])).
% 2.66/2.87  thf('170', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         ((r2_hidden @ X0 @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 2.66/2.87          | ~ (v1_xboole_0 @ X0))),
% 2.66/2.87      inference('sup+', [status(thm)], ['90', '169'])).
% 2.66/2.87  thf('171', plain,
% 2.66/2.87      (![X4 : $i, X6 : $i]:
% 2.66/2.87         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 2.66/2.87      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.87  thf('172', plain,
% 2.66/2.87      (![X0 : $i]:
% 2.66/2.87         (~ (v1_xboole_0 @ 
% 2.66/2.87             (sk_C @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0) @ X0))
% 2.66/2.87          | (r1_tarski @ X0 @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['170', '171'])).
% 2.66/2.87  thf('173', plain,
% 2.66/2.87      (((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 2.66/2.87         (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))
% 2.66/2.87        | (r1_tarski @ 
% 2.66/2.87           (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 2.66/2.87           (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.66/2.87      inference('sup-', [status(thm)], ['89', '172'])).
% 2.66/2.87  thf('174', plain,
% 2.66/2.87      ((r1_tarski @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 2.66/2.87        (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 2.66/2.87      inference('simplify', [status(thm)], ['173'])).
% 2.66/2.87  thf('175', plain, ($false), inference('demod', [status(thm)], ['71', '174'])).
% 2.66/2.87  
% 2.66/2.87  % SZS output end Refutation
% 2.66/2.87  
% 2.66/2.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
