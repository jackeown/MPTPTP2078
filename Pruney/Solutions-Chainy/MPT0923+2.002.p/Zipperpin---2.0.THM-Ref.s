%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lfvxEyargC

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:16 EST 2020

% Result     : Theorem 6.80s
% Output     : Refutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 822 expanded)
%              Number of leaves         :   33 ( 267 expanded)
%              Depth                    :   25
%              Number of atoms          : 1617 (7109 expanded)
%              Number of equality atoms :  183 ( 499 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t83_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
        & ! [F: $i,G: $i,H: $i,I: $i] :
            ~ ( ( r2_hidden @ F @ B )
              & ( r2_hidden @ G @ C )
              & ( r2_hidden @ H @ D )
              & ( r2_hidden @ I @ E )
              & ( A
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ~ ( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) )
          & ! [F: $i,G: $i,H: $i,I: $i] :
              ~ ( ( r2_hidden @ F @ B )
                & ( r2_hidden @ G @ C )
                & ( r2_hidden @ H @ D )
                & ( r2_hidden @ I @ E )
                & ( A
                  = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l68_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ? [E: $i] :
            ( ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ B )
                   => ! [H: $i] :
                        ( ( m1_subset_1 @ H @ C )
                       => ! [I: $i] :
                            ( ( m1_subset_1 @ I @ D )
                           => ( E
                             != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )
            & ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X26 @ X27 @ X25 @ X24 @ X23 ) @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('7',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X26 @ X27 @ X25 @ X24 @ X23 ) @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('12',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X26 @ X27 @ X25 @ X24 @ X23 ) @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('17',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X26
        = ( k4_mcart_1 @ ( sk_F @ X26 @ X27 @ X25 @ X24 @ X23 ) @ ( sk_G @ X26 @ X27 @ X25 @ X24 @ X23 ) @ ( sk_H @ X26 @ X27 @ X25 @ X24 @ X23 ) @ ( sk_I @ X26 @ X27 @ X25 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('22',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_A
      = ( k4_mcart_1 @ ( sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ ( sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) ) )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X26 @ X27 @ X25 @ X24 @ X23 ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('25',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_B )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_B )
      | ~ ( r2_hidden @ X37 @ sk_C_1 )
      | ~ ( r2_hidden @ X38 @ sk_D )
      | ( sk_A
       != ( k4_mcart_1 @ X36 @ X37 @ X38 @ X39 ) )
      | ~ ( r2_hidden @ X39 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( sk_A
       != ( k4_mcart_1 @ ( sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D )
    | ~ ( r2_hidden @ ( sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_E )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r2_hidden @ ( sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_E )
    | ~ ( r2_hidden @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r2_hidden @ ( sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_D )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r2_hidden @ ( sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_E )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_E )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('38',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('45',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('63',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','76'])).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('91',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('97',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('99',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('102',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('106',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','58'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['2','99','132','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lfvxEyargC
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.80/7.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.80/7.02  % Solved by: fo/fo7.sh
% 6.80/7.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.80/7.02  % done 10129 iterations in 6.562s
% 6.80/7.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.80/7.02  % SZS output start Refutation
% 6.80/7.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.80/7.02  thf(sk_E_type, type, sk_E: $i).
% 6.80/7.02  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 6.80/7.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.80/7.02  thf(sk_D_type, type, sk_D: $i).
% 6.80/7.02  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 6.80/7.02  thf(sk_A_type, type, sk_A: $i).
% 6.80/7.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.80/7.02  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 6.80/7.02  thf(sk_B_type, type, sk_B: $i).
% 6.80/7.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.80/7.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.80/7.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.80/7.02  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 6.80/7.02  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 6.80/7.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.80/7.02  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 6.80/7.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.80/7.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.80/7.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.80/7.02  thf(t83_mcart_1, conjecture,
% 6.80/7.02    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.80/7.02     ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 6.80/7.02          ( ![F:$i,G:$i,H:$i,I:$i]:
% 6.80/7.02            ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 6.80/7.02                 ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 6.80/7.02                 ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 6.80/7.02  thf(zf_stmt_0, negated_conjecture,
% 6.80/7.02    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.80/7.02        ( ~( ( r2_hidden @ A @ ( k4_zfmisc_1 @ B @ C @ D @ E ) ) & 
% 6.80/7.02             ( ![F:$i,G:$i,H:$i,I:$i]:
% 6.80/7.02               ( ~( ( r2_hidden @ F @ B ) & ( r2_hidden @ G @ C ) & 
% 6.80/7.02                    ( r2_hidden @ H @ D ) & ( r2_hidden @ I @ E ) & 
% 6.80/7.02                    ( ( A ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) )),
% 6.80/7.02    inference('cnf.neg', [status(esa)], [t83_mcart_1])).
% 6.80/7.02  thf('0', plain,
% 6.80/7.02      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.02  thf(t7_boole, axiom,
% 6.80/7.02    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 6.80/7.02  thf('1', plain,
% 6.80/7.02      (![X13 : $i, X14 : $i]:
% 6.80/7.02         (~ (r2_hidden @ X13 @ X14) | ~ (v1_xboole_0 @ X14))),
% 6.80/7.02      inference('cnf', [status(esa)], [t7_boole])).
% 6.80/7.02  thf('2', plain,
% 6.80/7.02      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.02      inference('sup-', [status(thm)], ['0', '1'])).
% 6.80/7.02  thf('3', plain,
% 6.80/7.02      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.02  thf(t1_subset, axiom,
% 6.80/7.02    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 6.80/7.02  thf('4', plain,
% 6.80/7.02      (![X19 : $i, X20 : $i]:
% 6.80/7.02         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 6.80/7.02      inference('cnf', [status(esa)], [t1_subset])).
% 6.80/7.02  thf('5', plain,
% 6.80/7.02      ((m1_subset_1 @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.02      inference('sup-', [status(thm)], ['3', '4'])).
% 6.80/7.02  thf(l68_mcart_1, axiom,
% 6.80/7.02    (![A:$i,B:$i,C:$i,D:$i]:
% 6.80/7.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 6.80/7.02          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 6.80/7.02          ( ?[E:$i]:
% 6.80/7.02            ( ( ![F:$i]:
% 6.80/7.02                ( ( m1_subset_1 @ F @ A ) =>
% 6.80/7.02                  ( ![G:$i]:
% 6.80/7.02                    ( ( m1_subset_1 @ G @ B ) =>
% 6.80/7.02                      ( ![H:$i]:
% 6.80/7.02                        ( ( m1_subset_1 @ H @ C ) =>
% 6.80/7.02                          ( ![I:$i]:
% 6.80/7.02                            ( ( m1_subset_1 @ I @ D ) =>
% 6.80/7.02                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 6.80/7.02              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 6.80/7.02  thf('6', plain,
% 6.80/7.02      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.80/7.02         (((X23) = (k1_xboole_0))
% 6.80/7.02          | ((X24) = (k1_xboole_0))
% 6.80/7.02          | ((X25) = (k1_xboole_0))
% 6.80/7.02          | (m1_subset_1 @ (sk_G @ X26 @ X27 @ X25 @ X24 @ X23) @ X24)
% 6.80/7.02          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 6.80/7.03          | ((X27) = (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [l68_mcart_1])).
% 6.80/7.03  thf('7', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (m1_subset_1 @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['5', '6'])).
% 6.80/7.03  thf(t2_subset, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( m1_subset_1 @ A @ B ) =>
% 6.80/7.03       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 6.80/7.03  thf('8', plain,
% 6.80/7.03      (![X21 : $i, X22 : $i]:
% 6.80/7.03         ((r2_hidden @ X21 @ X22)
% 6.80/7.03          | (v1_xboole_0 @ X22)
% 6.80/7.03          | ~ (m1_subset_1 @ X21 @ X22))),
% 6.80/7.03      inference('cnf', [status(esa)], [t2_subset])).
% 6.80/7.03  thf('9', plain,
% 6.80/7.03      ((((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_C_1)
% 6.80/7.03        | (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['7', '8'])).
% 6.80/7.03  thf('10', plain,
% 6.80/7.03      ((m1_subset_1 @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['3', '4'])).
% 6.80/7.03  thf('11', plain,
% 6.80/7.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.80/7.03         (((X23) = (k1_xboole_0))
% 6.80/7.03          | ((X24) = (k1_xboole_0))
% 6.80/7.03          | ((X25) = (k1_xboole_0))
% 6.80/7.03          | (m1_subset_1 @ (sk_H @ X26 @ X27 @ X25 @ X24 @ X23) @ X25)
% 6.80/7.03          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 6.80/7.03          | ((X27) = (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [l68_mcart_1])).
% 6.80/7.03  thf('12', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (m1_subset_1 @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D)
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['10', '11'])).
% 6.80/7.03  thf('13', plain,
% 6.80/7.03      (![X21 : $i, X22 : $i]:
% 6.80/7.03         ((r2_hidden @ X21 @ X22)
% 6.80/7.03          | (v1_xboole_0 @ X22)
% 6.80/7.03          | ~ (m1_subset_1 @ X21 @ X22))),
% 6.80/7.03      inference('cnf', [status(esa)], [t2_subset])).
% 6.80/7.03  thf('14', plain,
% 6.80/7.03      ((((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_D)
% 6.80/7.03        | (r2_hidden @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D))),
% 6.80/7.03      inference('sup-', [status(thm)], ['12', '13'])).
% 6.80/7.03  thf('15', plain,
% 6.80/7.03      ((m1_subset_1 @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['3', '4'])).
% 6.80/7.03  thf('16', plain,
% 6.80/7.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.80/7.03         (((X23) = (k1_xboole_0))
% 6.80/7.03          | ((X24) = (k1_xboole_0))
% 6.80/7.03          | ((X25) = (k1_xboole_0))
% 6.80/7.03          | (m1_subset_1 @ (sk_I @ X26 @ X27 @ X25 @ X24 @ X23) @ X27)
% 6.80/7.03          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 6.80/7.03          | ((X27) = (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [l68_mcart_1])).
% 6.80/7.03  thf('17', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (m1_subset_1 @ (sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_E)
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['15', '16'])).
% 6.80/7.03  thf('18', plain,
% 6.80/7.03      (![X21 : $i, X22 : $i]:
% 6.80/7.03         ((r2_hidden @ X21 @ X22)
% 6.80/7.03          | (v1_xboole_0 @ X22)
% 6.80/7.03          | ~ (m1_subset_1 @ X21 @ X22))),
% 6.80/7.03      inference('cnf', [status(esa)], [t2_subset])).
% 6.80/7.03  thf('19', plain,
% 6.80/7.03      ((((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_E)
% 6.80/7.03        | (r2_hidden @ (sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['17', '18'])).
% 6.80/7.03  thf('20', plain,
% 6.80/7.03      ((m1_subset_1 @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['3', '4'])).
% 6.80/7.03  thf('21', plain,
% 6.80/7.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.80/7.03         (((X23) = (k1_xboole_0))
% 6.80/7.03          | ((X24) = (k1_xboole_0))
% 6.80/7.03          | ((X25) = (k1_xboole_0))
% 6.80/7.03          | ((X26)
% 6.80/7.03              = (k4_mcart_1 @ (sk_F @ X26 @ X27 @ X25 @ X24 @ X23) @ 
% 6.80/7.03                 (sk_G @ X26 @ X27 @ X25 @ X24 @ X23) @ 
% 6.80/7.03                 (sk_H @ X26 @ X27 @ X25 @ X24 @ X23) @ 
% 6.80/7.03                 (sk_I @ X26 @ X27 @ X25 @ X24 @ X23)))
% 6.80/7.03          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 6.80/7.03          | ((X27) = (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [l68_mcart_1])).
% 6.80/7.03  thf('22', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_A)
% 6.80/7.03            = (k4_mcart_1 @ (sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ 
% 6.80/7.03               (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ 
% 6.80/7.03               (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ 
% 6.80/7.03               (sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B)))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['20', '21'])).
% 6.80/7.03  thf('23', plain,
% 6.80/7.03      ((m1_subset_1 @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['3', '4'])).
% 6.80/7.03  thf('24', plain,
% 6.80/7.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.80/7.03         (((X23) = (k1_xboole_0))
% 6.80/7.03          | ((X24) = (k1_xboole_0))
% 6.80/7.03          | ((X25) = (k1_xboole_0))
% 6.80/7.03          | (m1_subset_1 @ (sk_F @ X26 @ X27 @ X25 @ X24 @ X23) @ X23)
% 6.80/7.03          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X23 @ X24 @ X25 @ X27))
% 6.80/7.03          | ((X27) = (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [l68_mcart_1])).
% 6.80/7.03  thf('25', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (m1_subset_1 @ (sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_B)
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['23', '24'])).
% 6.80/7.03  thf('26', plain,
% 6.80/7.03      (![X21 : $i, X22 : $i]:
% 6.80/7.03         ((r2_hidden @ X21 @ X22)
% 6.80/7.03          | (v1_xboole_0 @ X22)
% 6.80/7.03          | ~ (m1_subset_1 @ X21 @ X22))),
% 6.80/7.03      inference('cnf', [status(esa)], [t2_subset])).
% 6.80/7.03  thf('27', plain,
% 6.80/7.03      ((((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_B)
% 6.80/7.03        | (r2_hidden @ (sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['25', '26'])).
% 6.80/7.03  thf('28', plain,
% 6.80/7.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 6.80/7.03         (~ (r2_hidden @ X36 @ sk_B)
% 6.80/7.03          | ~ (r2_hidden @ X37 @ sk_C_1)
% 6.80/7.03          | ~ (r2_hidden @ X38 @ sk_D)
% 6.80/7.03          | ((sk_A) != (k4_mcart_1 @ X36 @ X37 @ X38 @ X39))
% 6.80/7.03          | ~ (r2_hidden @ X39 @ sk_E))),
% 6.80/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.03  thf('29', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         ((v1_xboole_0 @ sk_B)
% 6.80/7.03          | ((sk_E) = (k1_xboole_0))
% 6.80/7.03          | ((sk_D) = (k1_xboole_0))
% 6.80/7.03          | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03          | ((sk_B) = (k1_xboole_0))
% 6.80/7.03          | ~ (r2_hidden @ X0 @ sk_E)
% 6.80/7.03          | ((sk_A)
% 6.80/7.03              != (k4_mcart_1 @ (sk_F @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ 
% 6.80/7.03                  X2 @ X1 @ X0))
% 6.80/7.03          | ~ (r2_hidden @ X1 @ sk_D)
% 6.80/7.03          | ~ (r2_hidden @ X2 @ sk_C_1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['27', '28'])).
% 6.80/7.03  thf('30', plain,
% 6.80/7.03      ((((sk_A) != (sk_A))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | ~ (r2_hidden @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D)
% 6.80/7.03        | ~ (r2_hidden @ (sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_E)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['22', '29'])).
% 6.80/7.03  thf('31', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_B)
% 6.80/7.03        | ~ (r2_hidden @ (sk_I @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_E)
% 6.80/7.03        | ~ (r2_hidden @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D)
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('simplify', [status(thm)], ['30'])).
% 6.80/7.03  thf('32', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_E)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | ~ (r2_hidden @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D)
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['19', '31'])).
% 6.80/7.03  thf('33', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_B)
% 6.80/7.03        | ~ (r2_hidden @ (sk_H @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_D)
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_E))),
% 6.80/7.03      inference('simplify', [status(thm)], ['32'])).
% 6.80/7.03  thf('34', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_D)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_E)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['14', '33'])).
% 6.80/7.03  thf('35', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_B)
% 6.80/7.03        | ~ (r2_hidden @ (sk_G @ sk_A @ sk_E @ sk_D @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.80/7.03        | (v1_xboole_0 @ sk_E)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_D))),
% 6.80/7.03      inference('simplify', [status(thm)], ['34'])).
% 6.80/7.03  thf('36', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_C_1)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_D)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_E)
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['9', '35'])).
% 6.80/7.03  thf('37', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_B)
% 6.80/7.03        | (v1_xboole_0 @ sk_E)
% 6.80/7.03        | (v1_xboole_0 @ sk_D)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_C_1))),
% 6.80/7.03      inference('simplify', [status(thm)], ['36'])).
% 6.80/7.03  thf(t53_mcart_1, axiom,
% 6.80/7.03    (![A:$i,B:$i,C:$i,D:$i]:
% 6.80/7.03     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 6.80/7.03       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 6.80/7.03  thf('38', plain,
% 6.80/7.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 6.80/7.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34) @ 
% 6.80/7.03              X35))),
% 6.80/7.03      inference('cnf', [status(esa)], [t53_mcart_1])).
% 6.80/7.03  thf(fc3_zfmisc_1, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 6.80/7.03  thf('39', plain,
% 6.80/7.03      (![X15 : $i, X16 : $i]:
% 6.80/7.03         ((v1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 6.80/7.03  thf(t3_xboole_0, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 6.80/7.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.80/7.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.80/7.03            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.80/7.03  thf('40', plain,
% 6.80/7.03      (![X4 : $i, X5 : $i]:
% 6.80/7.03         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 6.80/7.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.80/7.03  thf('41', plain,
% 6.80/7.03      (![X13 : $i, X14 : $i]:
% 6.80/7.03         (~ (r2_hidden @ X13 @ X14) | ~ (v1_xboole_0 @ X14))),
% 6.80/7.03      inference('cnf', [status(esa)], [t7_boole])).
% 6.80/7.03  thf('42', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['40', '41'])).
% 6.80/7.03  thf(d7_xboole_0, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( r1_xboole_0 @ A @ B ) <=>
% 6.80/7.03       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 6.80/7.03  thf('43', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 6.80/7.03      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.80/7.03  thf('44', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['42', '43'])).
% 6.80/7.03  thf(idempotence_k3_xboole_0, axiom,
% 6.80/7.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 6.80/7.03  thf('45', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 6.80/7.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 6.80/7.03  thf('46', plain,
% 6.80/7.03      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup+', [status(thm)], ['44', '45'])).
% 6.80/7.03  thf('47', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['39', '46'])).
% 6.80/7.03  thf('48', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.80/7.03         (((k1_xboole_0) = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup+', [status(thm)], ['38', '47'])).
% 6.80/7.03  thf('49', plain,
% 6.80/7.03      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['0', '1'])).
% 6.80/7.03  thf('50', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_E))),
% 6.80/7.03      inference('sup-', [status(thm)], ['48', '49'])).
% 6.80/7.03  thf('51', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 6.80/7.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 6.80/7.03  thf('52', plain,
% 6.80/7.03      (![X0 : $i, X2 : $i]:
% 6.80/7.03         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 6.80/7.03      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.80/7.03  thf('53', plain,
% 6.80/7.03      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['51', '52'])).
% 6.80/7.03  thf('54', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('simplify', [status(thm)], ['53'])).
% 6.80/7.03  thf(t69_xboole_1, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.80/7.03       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 6.80/7.03  thf('55', plain,
% 6.80/7.03      (![X11 : $i, X12 : $i]:
% 6.80/7.03         (~ (r1_xboole_0 @ X11 @ X12)
% 6.80/7.03          | ~ (r1_tarski @ X11 @ X12)
% 6.80/7.03          | (v1_xboole_0 @ X11))),
% 6.80/7.03      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.80/7.03  thf('56', plain,
% 6.80/7.03      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['54', '55'])).
% 6.80/7.03  thf(d10_xboole_0, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.80/7.03  thf('57', plain,
% 6.80/7.03      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 6.80/7.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.80/7.03  thf('58', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 6.80/7.03      inference('simplify', [status(thm)], ['57'])).
% 6.80/7.03  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('60', plain, (~ (v1_xboole_0 @ sk_E)),
% 6.80/7.03      inference('demod', [status(thm)], ['50', '59'])).
% 6.80/7.03  thf('61', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_C_1)
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_D)
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['37', '60'])).
% 6.80/7.03  thf('62', plain,
% 6.80/7.03      (![X15 : $i, X16 : $i]:
% 6.80/7.03         ((v1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 6.80/7.03  thf('63', plain,
% 6.80/7.03      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.03  thf('64', plain,
% 6.80/7.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 6.80/7.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34) @ 
% 6.80/7.03              X35))),
% 6.80/7.03      inference('cnf', [status(esa)], [t53_mcart_1])).
% 6.80/7.03  thf(fc4_zfmisc_1, axiom,
% 6.80/7.03    (![A:$i,B:$i]:
% 6.80/7.03     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 6.80/7.03  thf('65', plain,
% 6.80/7.03      (![X17 : $i, X18 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X17) | (v1_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 6.80/7.03  thf('66', plain,
% 6.80/7.03      (![X4 : $i, X5 : $i]:
% 6.80/7.03         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 6.80/7.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.80/7.03  thf('67', plain,
% 6.80/7.03      (![X13 : $i, X14 : $i]:
% 6.80/7.03         (~ (r2_hidden @ X13 @ X14) | ~ (v1_xboole_0 @ X14))),
% 6.80/7.03      inference('cnf', [status(esa)], [t7_boole])).
% 6.80/7.03  thf('68', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['66', '67'])).
% 6.80/7.03  thf('69', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1) | (r1_xboole_0 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['65', '68'])).
% 6.80/7.03  thf('70', plain,
% 6.80/7.03      ((r2_hidden @ sk_A @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E))),
% 6.80/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.80/7.03  thf('71', plain,
% 6.80/7.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 6.80/7.03         (~ (r2_hidden @ X6 @ X4)
% 6.80/7.03          | ~ (r2_hidden @ X6 @ X7)
% 6.80/7.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 6.80/7.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.80/7.03  thf('72', plain,
% 6.80/7.03      (![X0 : $i]:
% 6.80/7.03         (~ (r1_xboole_0 @ (k4_zfmisc_1 @ sk_B @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 6.80/7.03          | ~ (r2_hidden @ sk_A @ X0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['70', '71'])).
% 6.80/7.03  thf('73', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1) | ~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['69', '72'])).
% 6.80/7.03  thf('74', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.80/7.03         (~ (r2_hidden @ sk_A @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['64', '73'])).
% 6.80/7.03  thf('75', plain,
% 6.80/7.03      (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ sk_D))),
% 6.80/7.03      inference('sup-', [status(thm)], ['63', '74'])).
% 6.80/7.03  thf('76', plain, (~ (v1_xboole_0 @ sk_D)),
% 6.80/7.03      inference('sup-', [status(thm)], ['62', '75'])).
% 6.80/7.03  thf('77', plain,
% 6.80/7.03      (((v1_xboole_0 @ sk_B)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_C_1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['61', '76'])).
% 6.80/7.03  thf('78', plain,
% 6.80/7.03      (![X15 : $i, X16 : $i]:
% 6.80/7.03         ((v1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 6.80/7.03  thf('79', plain,
% 6.80/7.03      (![X17 : $i, X18 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X17) | (v1_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 6.80/7.03  thf('80', plain,
% 6.80/7.03      (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ sk_D))),
% 6.80/7.03      inference('sup-', [status(thm)], ['63', '74'])).
% 6.80/7.03  thf('81', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['79', '80'])).
% 6.80/7.03  thf('82', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 6.80/7.03      inference('sup-', [status(thm)], ['78', '81'])).
% 6.80/7.03  thf('83', plain,
% 6.80/7.03      ((((sk_E) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | (v1_xboole_0 @ sk_B))),
% 6.80/7.03      inference('sup-', [status(thm)], ['77', '82'])).
% 6.80/7.03  thf('84', plain,
% 6.80/7.03      (![X17 : $i, X18 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X17) | (v1_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 6.80/7.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 6.80/7.03  thf('85', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['79', '80'])).
% 6.80/7.03  thf('86', plain, (~ (v1_xboole_0 @ sk_B)),
% 6.80/7.03      inference('sup-', [status(thm)], ['84', '85'])).
% 6.80/7.03  thf('87', plain,
% 6.80/7.03      ((((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_E) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['83', '86'])).
% 6.80/7.03  thf('88', plain, (~ (v1_xboole_0 @ sk_E)),
% 6.80/7.03      inference('demod', [status(thm)], ['50', '59'])).
% 6.80/7.03  thf('89', plain,
% 6.80/7.03      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.80/7.03        | ((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['87', '88'])).
% 6.80/7.03  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('91', plain,
% 6.80/7.03      ((((sk_D) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0))
% 6.80/7.03        | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('demod', [status(thm)], ['89', '90'])).
% 6.80/7.03  thf('92', plain, (~ (v1_xboole_0 @ sk_D)),
% 6.80/7.03      inference('sup-', [status(thm)], ['62', '75'])).
% 6.80/7.03  thf('93', plain,
% 6.80/7.03      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.80/7.03        | ((sk_B) = (k1_xboole_0))
% 6.80/7.03        | ((sk_C_1) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['91', '92'])).
% 6.80/7.03  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('95', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 6.80/7.03      inference('demod', [status(thm)], ['93', '94'])).
% 6.80/7.03  thf('96', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 6.80/7.03      inference('sup-', [status(thm)], ['78', '81'])).
% 6.80/7.03  thf('97', plain,
% 6.80/7.03      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['95', '96'])).
% 6.80/7.03  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('99', plain, (((sk_B) = (k1_xboole_0))),
% 6.80/7.03      inference('demod', [status(thm)], ['97', '98'])).
% 6.80/7.03  thf('100', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 6.80/7.03      inference('simplify', [status(thm)], ['57'])).
% 6.80/7.03  thf('101', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['39', '46'])).
% 6.80/7.03  thf('102', plain,
% 6.80/7.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 6.80/7.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34) @ 
% 6.80/7.03              X35))),
% 6.80/7.03      inference('cnf', [status(esa)], [t53_mcart_1])).
% 6.80/7.03  thf('103', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.80/7.03         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X1))),
% 6.80/7.03      inference('sup+', [status(thm)], ['101', '102'])).
% 6.80/7.03  thf('104', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.80/7.03         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X1))),
% 6.80/7.03      inference('sup+', [status(thm)], ['101', '102'])).
% 6.80/7.03  thf('105', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1) | (r1_xboole_0 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['65', '68'])).
% 6.80/7.03  thf('106', plain,
% 6.80/7.03      (![X11 : $i, X12 : $i]:
% 6.80/7.03         (~ (r1_xboole_0 @ X11 @ X12)
% 6.80/7.03          | ~ (r1_tarski @ X11 @ X12)
% 6.80/7.03          | (v1_xboole_0 @ X11))),
% 6.80/7.03      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.80/7.03  thf('107', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1)
% 6.80/7.03          | (v1_xboole_0 @ X2)
% 6.80/7.03          | ~ (r1_tarski @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['105', '106'])).
% 6.80/7.03  thf('108', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.80/7.03         (~ (r1_tarski @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X1)
% 6.80/7.03          | (v1_xboole_0 @ X4)
% 6.80/7.03          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['104', '107'])).
% 6.80/7.03  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('110', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.80/7.03         (~ (r1_tarski @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X1)
% 6.80/7.03          | (v1_xboole_0 @ X4))),
% 6.80/7.03      inference('demod', [status(thm)], ['108', '109'])).
% 6.80/7.03  thf('111', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X4 : $i]:
% 6.80/7.03         (~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 6.80/7.03          | ~ (v1_xboole_0 @ X1)
% 6.80/7.03          | (v1_xboole_0 @ X4)
% 6.80/7.03          | ~ (v1_xboole_0 @ X1))),
% 6.80/7.03      inference('sup-', [status(thm)], ['103', '110'])).
% 6.80/7.03  thf('112', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X4 : $i]:
% 6.80/7.03         ((v1_xboole_0 @ X4)
% 6.80/7.03          | ~ (v1_xboole_0 @ X1)
% 6.80/7.03          | ~ (r1_tarski @ X4 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 6.80/7.03      inference('simplify', [status(thm)], ['111'])).
% 6.80/7.03  thf('113', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X1)
% 6.80/7.03          | (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['100', '112'])).
% 6.80/7.03  thf('114', plain,
% 6.80/7.03      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup+', [status(thm)], ['44', '45'])).
% 6.80/7.03  thf('115', plain,
% 6.80/7.03      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup+', [status(thm)], ['44', '45'])).
% 6.80/7.03  thf('116', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (((X0) = (X1)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 6.80/7.03      inference('sup+', [status(thm)], ['114', '115'])).
% 6.80/7.03  thf('117', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         (~ (v1_xboole_0 @ X2)
% 6.80/7.03          | ~ (v1_xboole_0 @ X1)
% 6.80/7.03          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (X1)))),
% 6.80/7.03      inference('sup-', [status(thm)], ['113', '116'])).
% 6.80/7.03  thf('118', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 6.80/7.03      inference('condensation', [status(thm)], ['117'])).
% 6.80/7.03  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('120', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['66', '67'])).
% 6.80/7.03  thf('121', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.80/7.03      inference('sup-', [status(thm)], ['119', '120'])).
% 6.80/7.03  thf('122', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 6.80/7.03      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.80/7.03  thf('123', plain,
% 6.80/7.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['121', '122'])).
% 6.80/7.03  thf('124', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i]:
% 6.80/7.03         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 6.80/7.03          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 6.80/7.03      inference('sup+', [status(thm)], ['118', '123'])).
% 6.80/7.03  thf('125', plain,
% 6.80/7.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.80/7.03      inference('sup-', [status(thm)], ['121', '122'])).
% 6.80/7.03  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('127', plain,
% 6.80/7.03      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.80/7.03      inference('demod', [status(thm)], ['124', '125', '126'])).
% 6.80/7.03  thf('128', plain,
% 6.80/7.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 6.80/7.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34) @ 
% 6.80/7.03              X35))),
% 6.80/7.03      inference('cnf', [status(esa)], [t53_mcart_1])).
% 6.80/7.03  thf('129', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 6.80/7.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0))),
% 6.80/7.03      inference('sup+', [status(thm)], ['127', '128'])).
% 6.80/7.03  thf('130', plain,
% 6.80/7.03      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.80/7.03      inference('demod', [status(thm)], ['124', '125', '126'])).
% 6.80/7.03  thf('131', plain,
% 6.80/7.03      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.80/7.03      inference('demod', [status(thm)], ['124', '125', '126'])).
% 6.80/7.03  thf('132', plain,
% 6.80/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.80/7.03         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0) = (k1_xboole_0))),
% 6.80/7.03      inference('demod', [status(thm)], ['129', '130', '131'])).
% 6.80/7.03  thf('133', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.80/7.03      inference('demod', [status(thm)], ['56', '58'])).
% 6.80/7.03  thf('134', plain, ($false),
% 6.80/7.03      inference('demod', [status(thm)], ['2', '99', '132', '133'])).
% 6.80/7.03  
% 6.80/7.03  % SZS output end Refutation
% 6.80/7.03  
% 6.80/7.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
