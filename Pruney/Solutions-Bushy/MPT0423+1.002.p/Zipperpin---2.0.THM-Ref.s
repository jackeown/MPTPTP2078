%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0423+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pi0jWusdUq

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:53 EST 2020

% Result     : Theorem 8.25s
% Output     : Refutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 932 expanded)
%              Number of leaves         :   30 ( 310 expanded)
%              Depth                    :   21
%              Number of atoms          : 1387 (7653 expanded)
%              Number of equality atoms :   61 ( 287 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t55_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B
          = ( k1_tarski @ A ) )
       => ( ( k7_setfam_1 @ A @ B )
          = ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B
            = ( k1_tarski @ A ) )
         => ( ( k7_setfam_1 @ A @ B )
            = ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k3_subset_1 @ X9 @ ( sk_D @ X8 @ X10 @ X9 ) ) @ X10 )
      | ( X8
        = ( k7_setfam_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_tarski @ k1_xboole_0 )
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ X1 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ( X8
        = ( k7_setfam_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_tarski @ k1_xboole_0 )
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) )
      = sk_A )
    | ( ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_setfam_1 @ X17 @ ( k7_setfam_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( X8
       != ( k7_setfam_1 @ X9 @ X10 ) )
      | ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X9 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X9 @ X11 ) @ X10 )
      | ( r2_hidden @ X11 @ ( k7_setfam_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','49'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('53',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X9 @ X11 ) @ X10 )
      | ( r2_hidden @ X11 @ ( k7_setfam_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X21: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X23 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['68','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( X8
       != ( k7_setfam_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X9 @ X11 ) @ X10 )
      | ~ ( r2_hidden @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('84',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( k7_setfam_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X9 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('89',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','94'])).

thf('96',plain,
    ( ( ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','95'])).

thf('97',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('98',plain,
    ( ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('100',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X9 @ ( sk_D @ X8 @ X10 @ X9 ) ) @ X10 )
      | ( X8
        = ( k7_setfam_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_tarski @ k1_xboole_0 )
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ X1 @ X0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('104',plain,
    ( ( sk_D @ ( k1_tarski @ k1_xboole_0 ) @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['96','97'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('106',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('108',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','103','104','105','108','109'])).

thf('111',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).


%------------------------------------------------------------------------------
